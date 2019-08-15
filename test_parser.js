
tests = {
    
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

    cnf2_TODO: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((p∧(Fa∧Fb))∨(p∧(Fc∧Fd)))∧((q∧(Fe∧Ff))∨(q∧(Fg∧Fh)))');
        var cnf = parser.cnf(f);
        assertEqual(cnf.toString(), '');
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
