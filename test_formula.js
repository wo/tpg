
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
    
    parseAxFxandNegate: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀xFx');
        assertEqual(f.type, 'gamma');
        assertEqual(f.variables.length, 1);
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

    variables: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x∃zHxf(x)z ∨ ∃v∀wGvw');
        var innerEx = f.sub1.matrix.matrix;
        assertEqual(innerEx.variables.toString(), '[x,z]');
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

    cnf: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((a∧b)∨(c∧d))∨e');
        var cnf = f.cnf();
        assertEqual(cnf.toString(), '[[a,c,e],[a,d,e],[b,c,e],[b,d,e]]');
    },

    cnf2_TODO: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((p∧(Fa∧Fb))∨(p∧(Fc∧Fd)))∧((q∧(Fe∧Ff))∨(q∧(Fg∧Fh)))');
        var cnf = f.cnf();
        assertEqual(cnf.toString(), '');
    },

    cnf3: function() {
        var parser = new Parser();
        var f = parser.parseFormula("(¬Px∨((¬Py∨Pf(xy))∧(Qxg(x)∧(¬Pg(x)∨¬Rcg(x)))))");
        var cnf = f.cnf();
        assertEqual(cnf.toString(), '[[¬Px,¬Py,Pf(xy)],[¬Px,Qxg(x)],[¬Px,¬Pg(x),¬Rcg(x)]]');
    },

    skolemize: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x∃y(Fx∧∀zHxyz)');
        f = f.normalize();
        var sk = f.skolemize();
        assertEqual(sk.toString(), '∀x(Fx∧∀zHxf(x)z)');
    },
    
    skolemize2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x∃y∃zHxyz ∨ ∃v∀wGvw');
        f = f.normalize();
        var sk = f.skolemize();
        assertEqual(sk.toString(), '(∀xHxf(x)g(x)∨∀wGaw)');
    },
    
    clausalNormalForm1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x∃y(Fx∧∀zHxyz)');
        f = f.normalize();
        var cnf = f.clausalNormalForm();
        assertEqual(cnf.toString(), '[[Fx],[Hxf(x)z]]');
    },

    clausalNormalForm: function() {
        // example from http://www8.cs.umu.se/kurser/TDBB08/vt98b/Slides4/norm1_4.pdf
        var parser = new Parser();
        //var f = parser.parseFormula('∀x(Px→(∀y((Py→Pf(x,y))∧¬∀y(Qxy→(Py∧Rcy))))))');
        var f = parser.parseFormula('∀x(Px→(∀y(Py→Pf(x,y)))∧¬∀y(Qxy→(Py∧Rcy)))');
        f = f.normalize();
        var cnf = f.clausalNormalForm();
        assertEqual(cnf.toString(), '[[¬Px,¬Py,Pf(xy)],[¬Px,Qxg(x)],[¬Px,¬Pg(x),¬Rcg(x)]]');
    },

    unify: function() {
        var parser = new Parser();
        var f1 = parser.parseFormula('Ff(a,b)');
        var f2 = parser.parseFormula('Fξ1');
        var u = f1.unify(f2);
        assertEqual(u[0], 'ξ1');
        assertEqual(u[1].toString(), ['f','a','b']);
    },
    
    translateModal1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬p');
        var f2 = f.translateModal();
        assertEqual(f2.string, '¬pw');
    },

    translateModal2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p');
        var f2 = f.translateModal();
        assertEqual(f2.string, '∀v(Rwv→pv)');
    },

    translateModal3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p→p');
        var f2 = f.translateModal();
        assertEqual(f2.parser.arities['p'], 1);
        assertEqual(f2.parser.arities['w'], 0);
        assertEqual(f2.parser.expressionType['w'], 'world constant');
    },

    translateToModal: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p→◇p');
        var f2 = f.translateModal();
        var f3 = f2.translateToModal();
        assertEqual(f2.string, '□p→◇p');
    }

}
