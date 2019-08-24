
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
        assertEqual(f2.string, '∀v(Rwv→pv)');
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
        assertEqual(f3.string, '(□p→◇p)');
    },
    
    cnf: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((a∧b)∨(c∧d))∨e');
        var cnf = parser.cnf(f);
        assertEqual(cnf.toString(), '[[a,c,e],[a,d,e],[b,c,e],[b,d,e]]');
    },

    cnf2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((¬F∨G)∧(B∧¬W))∨((C∧¬E)∧(¬T∨D))');
        var cnf = parser.cnf(f);
        // wolframalpha: CNF (((~F || G) && (B && ~W)) || ((C && ~E) && (~T || D)))
        var correct = "[B,C],[B,D,¬T],[B,¬E],[C,¬F,G],[C,¬W],[D,¬F,G,¬T],[D,¬T,¬W],[¬E,¬F,G],[¬E,¬W]";
        var correct = '[[¬F,G,C],[¬F,G,¬E],[¬F,G,¬T,D],[B,C],[B,¬E],[B,¬T,D],[¬W,C],[¬W,¬E],[¬W,¬T,D]]';
        assertEqual(cnf.toString(), correct);
    },

    cnf3: function() {
        var parser = new Parser();
        var f = parser.parseFormula("(¬Px∨((¬Py∨Pf(xy))∧(Qxg(x)∧(¬Pg(x)∨¬Rcg(x)))))");
        var cnf = parser.cnf(f);
        assertEqual(cnf.toString(), '[[¬Px,¬Py,Pf(xy)],[¬Px,Qxg(x)],[¬Px,¬Pg(x),¬Rcg(x)]]');
    },

    skolemize: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x∃y(Fx∧∀zHxyz)');
        f = f.normalize();
        var sk = parser.skolemize(f);
        assertEqual(sk.toString(), '∀x(Fx∧∀zHxf(x)z)');
    },
    
    skolemize2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x∃y∃zHxyz ∨ ∃v∀wGvw');
        f = f.normalize();
        var sk = parser.skolemize(f);
        assertEqual(sk.toString(), '(∀xHxf(x)g(x)∨∀wGaw)');
    },
    
    clausalNormalForm1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x∃y(Fx∧∀zHxyz)');
        f = f.normalize();
        var cnf = parser.clausalNormalForm(f);
        assertEqual(cnf.toString(), '[[Fx],[Hxf(x)z]]');
    },

    clausalNormalForm2: function() {
        // example from http://www8.cs.umu.se/kurser/TDBB08/vt98b/Slides4/norm1_4.pdf
        var parser = new Parser();
        var f = parser.parseFormula('∀x(Px→(∀y(Py→Pf(x,y)))∧¬∀y(Qxy→(Py∧Rcy)))');
        f = f.normalize();
        var cnf = parser.clausalNormalForm(f);
        assertEqual(cnf.toString(), '[[¬Px,¬Py,Pf(xy)],[¬Px,Qxg(x)],[¬Px,¬Pg(x),¬Rcg(x)]]');
    },

    clausalNormalForm3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇p');
        f = parser.translateFromModal(f).normalize();
        var cnf = parser.clausalNormalForm(f);
        assertEqual(cnf.toString(), '[[Rwu],[pu]]');
        assertEqual(parser.expressionType['u'], 'world constant');
    }
    

}
