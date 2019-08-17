
tests = {

    parseAxFxandNegate: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀xFx');
        assertEqual(f.type, 'gamma');
        assertEqual(f.variable, 'x');
        var f2 = f.negate();
        assertEqual(f2.string, '¬∀xFx');
        assertEqual(f2.type, 'delta');
    },

    substitute: function() {
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
