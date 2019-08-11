
tests = {

    setup: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('Ff(a,a)')], parser);
        assert(mf.predicates.equals(['p','F']));
        assertEqual(mf.constants.toString(), '[a]');
        assertEqual(mf.funcSymbols.toString(), '[f]');
        assertEqual(mf.names.toString(), '[a]');
        assertEqual(mf.model.domain.length, 1);
        assertEqual(mf.model.worlds.length, 0);
    },


    makeconstraints_propositional: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('(r∧p)∨¬q'), parser.parseFormula('q∨(¬r∧s)')];
        var m = new ModelFinder(initflas, parser).model;
        assertEqual(m.constraints.toString(), '[[r,¬q],[p,¬q],[q,¬r],[q,s]]');
        assertEqual(m.constraintTerms.toString(), '[[],[],[],[]]');
        initflas.push(parser.parseFormula('Fa'));
        m = new ModelFinder(initflas, parser).model;
        assertEqual(m.constraints.toString(), '[[Fa],[r,¬q],[p,¬q],[q,¬r],[q,s]]');
        assertEqual(m.constraintTerms.toString(), '[[a],[],[],[],[]]');
    },

    makeconstraints_quantified1: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀xFx')];
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        assertEqual(m.constraints.toString(), '[[F0]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.constraints.toString(), '[[F0],[F1]]');
    },

    makeconstraints_quantified2: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃yGxy')];
        // skolemized: Gxf(x)
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        assertEqual(m.constraints.toString(), '[[G0f(0)]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.constraints.toString(), '[[G0f(0)],[G1f(1)]]');
        assertEqual(mf.constants.toString(), '[]');
    },

    makeconstraints_quantified3: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃y(Fx∧∀zHxyz)')];
        // skolemized: (Fx∧Hxf(x)z)
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        assertEqual(m.constraints.toString(), '[[F0],[H0f(0)0]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.constraints.toString(), '[[F0],[F1],[H0f(0)0],[H0f(0)1],[H1f(1)0],[H1f(1)1]]');
    },

    makeconstraints_modal1: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃y(Fx∧∀zHxyz)')];
        // skolemized: (Fx∧Hxf(x)z)
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        assertEqual(m.constraints.toString(), '[[F0],[H0f(0)0]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.constraints.toString(), '[[F0],[F1],[H0f(0)0],[H0f(0)1],[H1f(1)0],[H1f(1)1]]');
    },

    countermodel1: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬p')], parser);
        var res = mf.nextStep();
        assertEqual(res, true);
        assertEqual(mf.model.toString().trim(), 'p: false');
    },

    countermodel2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('¬q')], parser);
        var res = mf.nextStep();
        assertEqual(res, false);
        res = mf.nextStep();
        assertEqual(res, true);
        assertEqual(mf.model.toString().trim(), 'p: true\nq: false');
    },

    countermodel3: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a,b)')], parser);
        var res = mf.nextStep();
        assertEqual(res, true);
        assert(mf.model.toString().indexOf('f: { (0,0,0) }')>0);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Ff(a)∧¬Ff(f(a))').normalize();
        var mf = new ModelFinder([f], parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assert(mf.model.toString().indexOf('f: { (0,1), (1,0) }')>0);
        assert(mf.model.toString().indexOf('a: 0')>0);
        assert(mf.model.toString().indexOf('F: { 1 }')>0);
    },

    countermodel5: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀xFx')], parser);
        var m = mf.nextStep();
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel6: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('Fa ∧ ¬Fb')];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel7: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀x∃yRxy ∧ ¬∃xRxx').normalize()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('R: { (0,1), (1,0) }') > 0);
    },

    countermodel_shortestformulawith3individuals: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀y∃x(Ryx ∧ ¬Rxy)').normalize()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 3);
    },

    countermodel_shortestformulawith4individuals_FAILS: function() { // xxx TODO check why model doesn't switch to 4 individuals even after 10000 steps 
        var parser = new Parser();
        var fs = [parser.parseFormula('∀z∀y∃x(Rzx ∧ ¬Rxy)').normalize()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<100);
        assertEqual(mf.model.domain.length, 4);
    },

    countermodel_modal1: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('◇p'), parser.parseFormula('¬p')];
        fs = fs.map(function(f){return parser.translateFromModal(f).normalize()});
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 2);
        assert(mf.model.toString().indexOf('w: 0') > 0);
        assert(mf.model.toString().indexOf('R: { (0,1) }') > 0);
        assert(mf.model.toString().indexOf('p: { 1 }') > 0);
    },

    countermodel_modal2: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('□p→p')];
        fs = fs.map(function(f){return parser.translateFromModal(f).normalize()});
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assert(mf.model.toString().indexOf('R: { (0,0) }') > 0);
    },

    countermodel_modal3: function() {
        var parser = new Parser();
        var fs = [parser.translateFromModal(parser.parseFormula('□p')).normalize(),
                  parser.parseAccessibilityFormula('∀v∃u(Rvu)')];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assert(mf.model.toString().indexOf('w: 0') > 0);
        assert(mf.model.toString().indexOf('R: { (0,0) }') > 0);
        assert(mf.model.toString().indexOf('p: { 0 }') > 0);
    },

    
}
