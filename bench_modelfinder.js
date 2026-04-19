// Benchmark for modelfinder.
// Usage: node bench_modelfinder.js
//
// Runs modelfinder on every formula in examples_invalid.js (expecting a
// countermodel), prints statistics, then runs every formula in
// examples_valid.js with a 10-second timeout each (expecting no countermodel).

const fs = require('fs');
const path = require('path');

global.log = function() {};

const dir = __dirname;
for (const f of ['array', 'formula', 'parser', 'equality', 'modelfinder']) {
    let src = fs.readFileSync(path.join(dir, f + '.js'), 'utf8');
    src = src.split('\n').filter(line => !/^\s*log\(/.test(line)).join('\n');
    eval(src);
}

var invalidExamples = require('./examples_invalid.js');
var validExamples = require('./examples_valid.js');

var INVALID_TIMEOUT_MS = 60000;
var VALID_TIMEOUT_MS = 10000;

var name2fla = {
    "universality": "∀v∀uRvu",
    "reflexivity": "∀vRvv",
    "symmetry": "∀v∀u(Rvu→Ruv)",
    "transitivity": "∀v∀u∀t(Rvu→(Rut→Rvt))",
    "euclidity": "∀v∀u∀t(Rvu→(Rvt→Rut))",
    "seriality": "∀v∃uRvu"
};

function parseFormula(formulaStr) {
    var accessibilityConstraints = [];
    var bracketMatch = formulaStr.match(/\[([^\]]+)\]\s*$/);
    if (bracketMatch && bracketMatch[1].split(',').every(function(s) {
        return name2fla.hasOwnProperty(s.trim());
    })) {
        accessibilityConstraints = bracketMatch[1].split(',').map(function(s) { return s.trim(); });
        formulaStr = formulaStr.slice(0, bracketMatch.index).trim();
    }
    if (formulaStr.indexOf('||') > 0) {
        accessibilityConstraints = formulaStr.split('||')[1].split('|').map(function(s) { return s.trim(); });
        formulaStr = formulaStr.split('||')[0];
    }
    var s5 = accessibilityConstraints.indexOf('universality') > -1;
    var parser = new Parser();
    var parsedInput = parser.parseInput(formulaStr);
    var premises = parsedInput[0];
    var conclusion = parsedInput[1];
    var initFormulas = premises.concat([conclusion.negate()]);
    if (parser.isModal) {
        initFormulas = initFormulas.map(function(f) {
            return parser.translateFromModal(f);
        });
    }
    initFormulas = initFormulas.map(function(f) { return f.nnf(); });
    var accessibilityFormulas = accessibilityConstraints.map(function(s) {
        return parser.parseAccessibilityFormula(name2fla[s]).nnf();
    });
    return {
        parser: parser,
        formulas: initFormulas,
        accessibilityFormulas: accessibilityFormulas,
        s5: s5
    };
}

function runModelfinder(parsed, timeoutMs) {
    var mf = new ModelFinder(
        parsed.formulas,
        parsed.parser,
        parsed.accessibilityFormulas,
        parsed.s5
    );
    var t0 = performance.now();
    var deadline = t0 + timeoutMs;
    var steps = 0;
    while (performance.now() < deadline) {
        steps++;
        if (mf.nextStep()) {
            return { found: true, verified: mf.model.verifyModel(), steps: steps, elapsed: performance.now() - t0 };
        }
    }
    return { found: false, steps: steps, elapsed: performance.now() - t0 };
}

function formatTime(ms) {
    return (ms / 1000).toFixed(3) + 's';
}

function truncFormula(s) {
    s = String(s).replace(/\s+/g, ' ');
    return s.length > 80 ? s.slice(0, 77) + '...' : s;
}

function pad(str, len) {
    str = String(str);
    while (str.length < len) str += ' ';
    return str;
}

function rpad(str, len) {
    str = String(str);
    while (str.length < len) str = ' ' + str;
    return str;
}

console.log('=== Invalid formulas (' + invalidExamples.length + ', should find countermodel, timeout ' + (INVALID_TIMEOUT_MS/1000) + 's) ===');
console.log(pad('Label', 14) + pad('Formula', 82) + rpad('Steps', 10) + rpad('Time', 12) + '  Status');
console.log('-'.repeat(140));

var invalidTotalTime = 0;

for (var i = 0; i < invalidExamples.length; i++) {
    var ex = invalidExamples[i];
    var label = ex.label;
    var formula = ex.formula;
    var status, steps, elapsed;
    try {
        var parsed = parseFormula(formula);
        var result = runModelfinder(parsed, INVALID_TIMEOUT_MS);
        steps = result.steps;
        elapsed = result.elapsed;
        invalidTotalTime += elapsed;
        if (result.found) {
            status = result.verified ? 'ok' : 'BOGUS';
        } else {
            status = 'TIMEOUT';
        }
    } catch (e) {
        status = 'ERROR: ' + e.message;
        steps = '-';
        elapsed = 0;
    }
    console.log(pad(label, 14) + pad(truncFormula(formula), 82) + rpad(steps, 10) + rpad(formatTime(elapsed), 12) + '  ' + status);
}

console.log('-'.repeat(140));
console.log('  Total time:      ' + formatTime(invalidTotalTime));

console.log('');
console.log('=== Valid formulas (' + validExamples.length + ', should NOT find countermodel, timeout ' + (VALID_TIMEOUT_MS/1000) + 's) ===');
console.log(pad('Label', 24) + pad('Formula', 82) + rpad('Steps', 10) + rpad('Time', 12) + '  Status');
console.log('-'.repeat(140));

var validTotalTime = 0;

for (var i = 0; i < validExamples.length; i++) {
    var ex = validExamples[i];
    var label = ex.label;
    var formula = ex.formula;
    var status, steps, elapsed;
    try {
        var parsed = parseFormula(formula);
        var result = runModelfinder(parsed, VALID_TIMEOUT_MS);
        steps = result.steps;
        elapsed = result.elapsed;
        validTotalTime += elapsed;
        if (result.found) {
            status = 'FAIL (spurious countermodel!)';
        } else {
            status = 'ok (no countermodel)';
        }
    } catch (e) {
        status = 'ERROR: ' + e.message;
        steps = '-';
        elapsed = 0;
    }
    console.log(pad(label, 24) + pad(truncFormula(formula), 82) + rpad(steps, 10) + rpad(formatTime(elapsed), 12) + '  ' + status);
}

console.log('-'.repeat(140));
console.log('  Total time:      ' + formatTime(validTotalTime));
