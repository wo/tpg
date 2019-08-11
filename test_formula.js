
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
    
    parseAxFxandNegate: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀xFx');
        assertEqual(f.type, 'gamma');
        assertEqual(f.variable, 'x');
        var f2 = f.negate();
        assertEqual(f2.string, '¬∀xFx');
        assertEqual(f2.type, 'delta');
    },

    parseAndSubstitute: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x(Fx → Fy)');
        var f2 = f.substitute('x', 'z');
        assertEqual(f, f2);
        var f2 = f.substitute('y', 'z');
        assertEqual(f2.string, '∀x(Fx→Fz)');
        assertEqual(f.string, '∀x(Fx→Fy)');
    },

    substitute2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(¬Av∨Bv)');
        var f2 = f.substitute('v', 'φ1');
        assertEqual(f2.string, '(¬Aφ1∨Bφ1)');
    },

    substituteComplex: function() {
        var parser = new Parser();
        var f = parser.parseFormula('H(a,b,g(c,c))');
        var f2 = f.substitute('c', ['f','a','b','c'], true);
        assertEqual(f, f2);
        var f2 = f.substitute('c', ['f','a','b','c']);
        assertEqual(f2.string, 'Habg(f(abc)f(abc))');
    },

    normalize: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∀x(Fx→Fx)').normalize();
        assertEqual(f, '∃x(Fx∧¬Fx)');
    },

    unify: function() {
        var parser = new Parser();
        var f1 = parser.parseFormula('Ff(a,b)');
        var f2 = parser.parseFormula('Fξ1');
        var u = f1.unify(f2);
        assertEqual(u[0], 'ξ1');
        assertEqual(u[1].toString(), ['f','a','b']);
    }
    
}
