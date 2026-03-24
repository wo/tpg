// CLI entry point for running the prover under Node.js.
// Usage: node prover_cli.js "<formula>" [--debug[=<module>]] [--trace]
//   --debug              show debug log output
//   --debug=modelfinder  show only modelfinder debug output
//   --trace              show trace log output

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
const cliParser = new Parser();
const [premises, conclusion] = cliParser.parseInput(formulaStr);
const initFormulas = premises.concat([conclusion.negate()]);
const cliProver = new Prover(initFormulas, cliParser, []);
cliProver.onfinished = (treeClosed) => {
    console.log(treeClosed ? 'VALID' : 'INVALID');
};
cliProver.start();
