// CLI entry point for running the prover under Node.js.
// Usage: node prover_cli.js "<formula>" [--debug[=<module>]] [--trace] [--prover9]
//   --debug              show debug log output
//   --debug=modelfinder  show only modelfinder debug output
//   --trace              show trace log output
//   --prover9            use Prover9/Mace4 instead of the built-in prover (C-c to abort)

const fs = require('fs');
const path = require('path');

const debugArg = process.argv.find(a => a === '--debug' || a.startsWith('--debug='));
const debugMode = !!debugArg;
const debugModule = debugArg && debugArg.includes('=') ? debugArg.split('=')[1] : null;
const traceMode = process.argv.includes('--trace');
global.log = (str, tracelog) => {
    if (traceMode ? tracelog : (debugMode && !tracelog)) console.log(('' + str).replace(/<br>/g, '\n').replace(/<[^>]*>/g, ''));
};

// Minimal stubs so index.js loads without a DOM:
global.window = {};
global.document = { getElementById: () => ({}), querySelector: () => null, querySelectorAll: () => [] };

// Load core files, stripping log() calls from files not selected for debugging:
const dir = __dirname;
function stripDebugging(src) {
    return src.split('\n').filter(line => !/^\s*log\(/.test(line)).join('\n');
}
for (const f of ['array', 'formula', 'parser', 'equality', 'modelfinder', 'sentree', 'prover', 'index']) {
    let src = fs.readFileSync(path.join(dir, f + '.js'), 'utf8');
    if (debugModule && f !== debugModule) src = stripDebugging(src);
    eval(src);
}

// Override Tree.prototype.toString to show branches as plain text lines in debugging:
Tree.prototype.toString = function() {
    const branches = this.closedBranches.concat(this.openBranches);
    const lines = branches.map((branch, i) => {
        const formulas = branch.nodes.map(n => n.formula.toString()).join(', ');
        const status = this.closedBranches.includes(branch) ? '[closed]' : '[open]';
        return `branch ${i+1} ${status}: ${formulas}`;
    });
    const open = this.openBranches[0];
    if (open) {
        lines.push('  todo: ' + open.todoList.map(t => Object.values(t)).join('; '));
        lines.push('  depth: ' + this.getNumNodes() + '-' + this.priority);
    }
    return lines.join('\n');
};

// Parse the input formula(s) and start the prover:
let formulaStr = process.argv.find((a, i) => i >= 2 && !a.startsWith('--'));
if (!formulaStr) {
    console.error('Usage: node prover_cli.js "<formula>" [--debug] [--trace]'); process.exit(1);
}
formulaStr = renderSymbols(formulaStr);

// Extract accessibility constraints from bracket notation, e.g. "[universality, reflexivity]"
var accessibilityConstraints = [];
var bracketMatch = formulaStr.match(/\[([^\]]+)\]\s*$/);
if (bracketMatch) {
    accessibilityConstraints = bracketMatch[1].split(',').map(s => s.trim());
    formulaStr = formulaStr.slice(0, bracketMatch.index).trim();
}

const cliParser = new Parser();
const [premises, conclusion] = cliParser.parseInput(formulaStr);
const initFormulas = premises.concat([conclusion.negate()]);

if (process.argv.includes('--prover9')) {
    // Use Prover9/Mace4 as external oracles
    const { spawnSync } = require('child_process');
    const PROVER9 = path.join(__dirname, 'Prover9/bin/prover9');
    const MACE4 = path.join(__dirname, 'Prover9/bin/mace4');

    // Prover9 translation. Caveats beyond naive conversion:
    //
    //   1. Free u-z identifiers. The JS parser treats free names as
    //      individual constants shared across premises and conclusion;
    //      Prover9 treats lowercase u-z names as variables and universally
    //      quantifies them in each list independently. So free identifiers
    //      starting with u-z get a `c_` prefix to become Prover9 constants.
    //
    //   2. Non-alphanumeric symbols like * and + would both collapse to `_`.
    //      Each such char is replaced by a codepoint token `_uNNN_` to
    //      preserve distinct symbol identity.
    //
    //   3. Sort relativization for modal formulas. The modal translation
    //      produces two-sorted formulas (objects and worlds); naively
    //      dropping them into single-sorted Prover9 conflates the sorts
    //      and yields unsound VALID verdicts. We introduce a unary
    //      predicate isWorld and relativize every quantifier to its sort.
    var isModal = cliParser.isModal;
    var W_PRED = 'isWorld';
    var nameCache = {};
    function sanitizeName(name, isFree) {
        var key = (isFree ? 'F:' : 'B:') + name;
        if (nameCache[key]) return nameCache[key];
        var result = name.replace(/[\u2080-\u2089]/g, ch => String(ch.charCodeAt(0) - 0x2080));
        result = result.replace(/[^a-zA-Z0-9_]/g, ch => '_u' + ch.charCodeAt(0) + '_');
        if (!/^[a-zA-Z]/.test(result)) result = 'c_' + result;
        if (isFree && /^[u-z]/.test(result)) result = 'c_' + result;
        if (['all','exists','not','or','and','if','iff','true','false',W_PRED].includes(result.toLowerCase())) {
            result = result + '_sym';
        }
        nameCache[key] = result;
        return result;
    }
    function isWorldSym(name) {
        var t = cliParser.expressionType[name];
        return t === 'world variable' || t === 'world constant';
    }
    function termToP9(t, bound) {
        if (t.isArray) {
            var parts = t.slice();
            var funcSym = parts.shift();
            return sanitizeName(funcSym, false) + '(' + parts.map(x => termToP9(x, bound)).join(',') + ')';
        }
        return sanitizeName(t, !bound.has(t));
    }
    function formulaToP9(fla, bound) {
        bound = bound || new Set();
        if (fla.quantifier) {
            var q = fla.quantifier === '∀' ? 'all' : 'exists';
            var nb = new Set(bound);
            nb.add(fla.variable);
            var varStr = sanitizeName(fla.variable, false);
            var body = formulaToP9(fla.matrix, nb);
            if (isModal) {
                var sortLit = (isWorldSym(fla.variable) ? '' : '-') + W_PRED + '(' + varStr + ')';
                var conn = q === 'all' ? ' -> ' : ' & ';
                return q + ' ' + varStr + ' (' + sortLit + conn + body + ')';
            }
            return q + ' ' + varStr + ' ' + body;
        }
        if (fla.operator === '¬') return '-(' + formulaToP9(fla.sub, bound) + ')';
        if (fla.sub1) {
            var op = { '∧':'&', '∨':'|', '→':'->', '↔':'<->' }[fla.operator] || fla.operator;
            return '(' + formulaToP9(fla.sub1, bound) + ' ' + op + ' ' + formulaToP9(fla.sub2, bound) + ')';
        }
        if (fla.predicate) {
            if (fla.predicate === '=') {
                return '(' + termToP9(fla.terms[0], bound) + ' = ' + termToP9(fla.terms[1], bound) + ')';
            }
            if (fla.terms.length === 0) return sanitizeName(fla.predicate, false);
            return sanitizeName(fla.predicate, false) + '(' + fla.terms.map(t => termToP9(t, bound)).join(',') + ')';
        }
        throw new Error('Unknown formula type');
    }
    function collectFreeIds(fla, bound, out) {
        if (fla.terms) {
            for (var t of fla.terms) collectFreeTermIds(t, bound, out);
        } else if (fla.quantifier) {
            var nb = new Set(bound); nb.add(fla.variable);
            collectFreeIds(fla.matrix, nb, out);
        } else if (fla.sub1) {
            collectFreeIds(fla.sub1, bound, out);
            collectFreeIds(fla.sub2, bound, out);
        } else if (fla.sub) {
            collectFreeIds(fla.sub, bound, out);
        }
    }
    function collectFreeTermIds(t, bound, out) {
        if (t.isArray) {
            for (var i = 1; i < t.length; i++) collectFreeTermIds(t[i], bound, out);
        } else if (!bound.has(t)) {
            out.add(t);
        }
    }

    var p9Premises = premises.slice();
    var p9Conclusion = conclusion;
    if (isModal) {
        p9Premises = p9Premises.map(f => cliParser.translateFromModal(f));
        p9Conclusion = cliParser.translateFromModal(p9Conclusion);
    }
    var accessibilityFormulas = [];
    if (accessibilityConstraints.length > 0) {
        var name2fla = {
            "universality": "∀v∀uRvu",
            "reflexivity": "∀vRvv",
            "symmetry": "∀v∀u(Rvu→Ruv)",
            "transitivity": "∀v∀u∀t(Rvu→(Rut→Rvt))",
            "euclidity": "∀v∀u∀t(Rvu→(Rvt→Rut))",
            "seriality": "∀v∃uRvu"
        };
        accessibilityFormulas = accessibilityConstraints.map(s => cliParser.parseAccessibilityFormula(name2fla[s]));
    }

    var sortAxiomLines = [];
    if (isModal) {
        var freeIds = new Set();
        for (var f of p9Premises) collectFreeIds(f, new Set(), freeIds);
        for (var f of accessibilityFormulas) collectFreeIds(f, new Set(), freeIds);
        collectFreeIds(p9Conclusion, new Set(), freeIds);
        for (var id of freeIds) {
            var s = sanitizeName(id, true);
            sortAxiomLines.push('  ' + (isWorldSym(id) ? '' : '-') + W_PRED + '(' + s + ').');
        }
        // Ensure the domain contains at least one object, so object quantifiers
        // can't be vacuously satisfied.
        sortAxiomLines.push('  exists x -' + W_PRED + '(x).');
    }

    var lines = [];
    if (p9Premises.length > 0 || accessibilityFormulas.length > 0 || sortAxiomLines.length > 0) {
        lines.push('formulas(sos).');
        for (var l of sortAxiomLines) lines.push(l);
        for (var f of accessibilityFormulas) lines.push('  ' + formulaToP9(f) + '.');
        for (var f of p9Premises) lines.push('  ' + formulaToP9(f) + '.');
        lines.push('end_of_list.');
    }
    lines.push('formulas(goals).');
    lines.push('  ' + formulaToP9(p9Conclusion) + '.');
    lines.push('end_of_list.');
    var p9input = lines.join('\n');

    if (debugMode) {
        console.log('=== Prover9 input ===');
        console.log(p9input);
        console.log('=====================');
    }

    function runTool(tool) {
        return spawnSync(tool, [], { input: p9input, encoding: 'utf8', maxBuffer: 10*1024*1024, stdio: ['pipe', 'pipe', 'pipe'] });
    }

    console.log('Running Prover9...');
    var p9 = runTool(PROVER9);
    if (/Exiting with \d+ proof/.test(p9.stdout || '')) {
        console.log('VALID');
        process.exit(0);
    }
    console.log('Running Mace4...');
    var m4 = runTool(MACE4);
    if (/Exiting with \d+ model/.test(m4.stdout || '')) {
        console.log('INVALID');
        process.exit(0);
    }
    console.log('UNKNOWN (neither proof nor countermodel found)');
    if (debugMode) {
        console.log('--- prover9 stdout tail ---');
        console.log((p9.stdout || '').split('\n').slice(-20).join('\n'));
        console.log('--- mace4 stdout tail ---');
        console.log((m4.stdout || '').split('\n').slice(-20).join('\n'));
    }
    process.exit(1);
}

if (process.argv.includes('--modelfinder-only')) {
    const mfParser = cliParser.copy();
    const mfFormulas = initFormulas.map(f => {
        var nf = cliParser.isModal ? mfParser.translateFromModal(f) : f;
        return nf.nnf();
    });
    var accessibilityFormulas = [];
    if (accessibilityConstraints.length > 0) {
        var name2fla = {
            "universality": "∀v∀uRvu",
            "reflexivity": "∀vRvv",
            "symmetry": "∀v∀u(Rvu→Ruv)",
            "transitivity": "∀v∀u∀t(Rvu→(Rut→Rvt))",
            "euclidity": "∀v∀u∀t(Rvu→(Rvt→Rut))",
            "seriality": "∀v∃uRvu"
        };
        accessibilityFormulas = accessibilityConstraints.map(function(s) {
            return mfParser.parseAccessibilityFormula(name2fla[s]).nnf();
        });
    }
    var s5 = accessibilityConstraints.includes('universality');
    const mf = new ModelFinder(mfFormulas, mfParser, accessibilityFormulas, s5);
    const maxSteps = parseInt(process.argv.find(a => a.startsWith('--max-steps='))?.split('=')[1]) || 500000;
    const t0 = performance.now();
    for (let i = 0; i < maxSteps; i++) {
        if (mf.nextStep()) {
            console.log('Model found in ' + (i+1) + ' steps (' + (performance.now()-t0).toFixed(0) + 'ms)');
            process.exit(0);
        }
    }
    console.log('No model in ' + maxSteps + ' steps (' + (performance.now()-t0).toFixed(0) + 'ms)');
    process.exit(1);
}
else {
    const cliProver = new Prover(initFormulas, cliParser, accessibilityConstraints);
    cliProver.pauseLength = 1;
    cliProver.onfinished = function(treeClosed) {
        console.log(treeClosed ? 'VALID' : 'INVALID');
        if (!treeClosed && this.counterModel) {
            console.log(this.counterModel.toString());
        }
    };
    cliProver.start();
}
