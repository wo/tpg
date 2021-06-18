
tests = {

    parseterms1: function() {
        var parser = new Parser();
        var t = parser.parseTerms('abc', []);
        assertEqual(t.length, 3)
        assertEqual(t[1], 'b')
    },

    parseterms2: function() {
        var parser = new Parser();
        var t = parser.parseTerms('f(a,b,g(c,c))', []);
        assertEqual(t.length, 1)
        assertEqual(t[0].length, 4)
        assertEqual(t[0][0], 'f')
        assertEqual(t[0][1], 'a')
        assertEqual(t[0][3].length, 3)
        assertEqual(t[0][3][0], 'g')
    },

    parsep: function() {
        var parser = new Parser();
        var f = parser.parseFormula('p');
        assertEqual(f.type, 'literal');
        assertEqual(f.toString(), 'p');
    },

    checkArities: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Ff(a)b');
        assertEqual(parser.arities['F'], 2);
        assertEqual(parser.arities['f'], 1);
    },
    
    parseGab: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Gab');
        assertEqual(f.type, 'literal');
        var f2 = parser.parseFormula('G(a,b)');
        assertEqual(f2.type, 'literal');
        assert(f.equals(f2));
    },

    parseF1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('F1');
        assertEqual(f.type, 'literal');
        assertEqual(f.predicate, 'F1');
        assertEqual(f.terms.length, 0);
    },

    parseNonWff: function() {
        var parser = new Parser();
        try {
            parser.parseFormula('□(∀x(¬Fx∧Fy) ↔ ∃xFx → □◇Fa');
            assert(false);
        }
        catch {
            assert(true);
        }
    },
    
    translateFromModal1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬p');
        var f2 = parser.translateFromModal(f);
        assertEqual(f2.string, '¬pw');
    },

    translateFromModal2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p');
        var f2 = parser.translateFromModal(f);
        assert(parser.isModal);
        assert(parser.isPropositional);
        assertEqual(f2.string, '∀v(Rwv → pv)');
    },

    translateFromModal3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p→p');
        var f2 = parser.translateFromModal(f);
        assertEqual(parser.arities['p'], 1);
        assertEqual(parser.arities['w'], 0);
        assertEqual(parser.expressionType['w'], 'world constant');
    },

    translateToModal: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p→◇p');
        var f2 = parser.translateFromModal(f);
        var f3 = parser.translateToModal(f2);
        assertEqual(f3.string, '(□p → ◇p)');
    },

    useRinModalFormula: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□R');
        var prover = new Prover([f], parser, ['symmetry']);
        // should not crash on double use of 'R'
        prover.pauseLength = 0;
        prover.start();
        assert(true);
    },

    parensAroundPremises: function() {
        var parser = new Parser();
        var res = parser.parseInput('(Ff(a,b), p) |= q');
        assertEqual(res[0].length, 2);
    },

    threePremises: function() {
        var parser = new Parser();
        var res = parser.parseInput('Ff(a,b), □p, (p∨q) |= q');
        assertEqual(res[0].length, 3);
    },

    parseK: function() {
        var parser = new Parser();
        var res = parser.parseInput('□(p→q)→□p→□q');
        assertEqual(res[1].string, '(□(p→q) → (□p → □q))');
    }

}
