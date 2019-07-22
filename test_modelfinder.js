
tests = {

    setup: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('Ff(a,a)')]);
        assert(mf.constants.equals(['f','a']));
        assert(mf.predicates.equals(['p','F']));
        assert(mf.terms.equals(['f(a,a)']));
        assertEqual(mf.model.domain.length, 1);
        assertEqual(mf.model.worlds.length, 0);
    },


    makeconstraints_propositional: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('(r∧p)∨¬q'), parser.parseFormula('q∨(¬r∧s)')];
        var m = new ModelFinder(initflas).model;
        assertEqual(m.constraints.toString(), '[[r,¬q],[p,¬q],[q,¬r],[q,s]]');
        assertEqual(m.constraintTerms.toString(), '[[],[],[],[]]');
        initflas.push(parser.parseFormula('Fa'));
        m = new ModelFinder(initflas).model;
        assertEqual(m.constraints.toString(), '[[Fa],[r,¬q],[p,¬q],[q,¬r],[q,s]]');
        assertEqual(m.constraintTerms.toString(), '[[a],[],[],[],[]]');
    },

    makeconstraints_quantified1: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀xFx')];
        var mf = new ModelFinder(initflas);
        var m = mf.model;
        assertEqual(m.constraints.toString(), '[[F0]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.constraints.toString(), '[[F0],[F1]]');
    },

    makeconstraints_quantified2: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃yGxy')];
        // skolemized: Gxf(x)
        var mf = new ModelFinder(initflas);
        var m = mf.model;
        assertEqual(m.constraints.toString(), '[[G0f(0)]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.constraints.toString(), '[[G0f(0)],[G1f(1)]]');
        assertEqual(mf.constants.toString(), '[f]');
        assertEqual(mf.origConstants.toString(), '[]');
    },

    makeconstraints_quantified3: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃y(Fx∧∀zHxyz)')];
        // skolemized: (Fx∧Hxf(x)z)
        var mf = new ModelFinder(initflas);
        var m = mf.model;
        assertEqual(m.constraints.toString(), '[[F0],[H0f(0)0]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.constraints.toString(), '[[F0],[F1],[H0f(0)0],[H0f(0)1],[H1f(1)0],[H1f(1)1]]');
    },

    countermodel1: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬p')]);
        var res = mf.nextStep();
        assertEqual(res, true);
        assertEqual(mf.model.toString().trim(), 'p: false');
    },

    countermodel2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('q')]);
        var res = mf.nextStep();
        assertEqual(res, false);
        res = mf.nextStep();
        assertEqual(res, true);
        assertEqual(mf.model.toString().trim(), 'p: true\nq: true');
    },

    countermodel3: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a,b)')]);
        var res = mf.nextStep();
        assertEqual(res, true);
        assert(mf.model.toString().indexOf('f: { (0,0,0) }')>0);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Ff(a)∧¬Ff(f(a))').normalize();
        var mf = new ModelFinder([f]);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assert(mf.model.toString().indexOf('f: { (1,0),(0,1) }')>0);
        assert(mf.model.toString().indexOf('a: 1')>0);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    satisfies: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬p'), parser.parseFormula('Ff(a,b)')]);
        mf.nextStep();
        mf.nextStep();
        assertEqual(mf.model.satisfies([parser.parseFormula('p')]), false);
        assertEqual(mf.model.satisfies([parser.parseFormula('¬p')]), true);
        assertEqual(mf.model.satisfies([parser.parseFormula('p'), parser.parseFormula('¬p')]), true);
        assertEqual(mf.model.satisfies([parser.parseFormula('Fa')]), false);
        assertEqual(mf.model.satisfies([parser.parseFormula('Ff(a,b)')]), false);
        assertEqual(mf.model.satisfies([parser.parseFormula('Ff(f(a,a),b)')]), false);
    },

    trynextmodel: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('q')]);
        var m = mf.tryNextModel();
        assertEqual(m, null);
        assertEqual(mf.model.getValue('p'), 0);
        assertEqual(mf.model.getValue('q'), undefined);
        var m = mf.tryNextModel();
        assertEqual(m, null);
        assertEqual(mf.model.getValue('p'), 1);
        var m = mf.tryNextModel();
        assertEqual(m, null);
        assertEqual(mf.model.getValue('p'), 1);
        assertEqual(mf.model.getValue('q'), 0);
        var m = mf.tryNextModel();
        assertEqual(m, mf.model);
        assertEqual(mf.model.getValue('p'), 1);
        assertEqual(mf.model.getValue('q'), 1);
    },
    
    trynextmodel2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬p'), parser.parseFormula('¬q')]);
        var m = mf.tryNextModel();
        assertEqual(m, null);
        assertEqual(mf.model.getValue('p'), 0);
        assertEqual(mf.model.getValue('q'), undefined);
        var m = mf.tryNextModel();
        assertEqual(m, mf.model);
        assertEqual(mf.model.getValue('p'), 0);
        assertEqual(mf.model.getValue('q'), 0);
    },

    trynextmodel3: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a,b)')]);
        var m = mf.tryNextModel();
        assertEqual(m, null);
        var m = mf.tryNextModel();
        assertEqual(m, mf.model);
    },

    trynextmodel4: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀xFx')]);
        var m = mf.tryNextModel();
        assertEqual(m, null);
        var m = mf.tryNextModel();
        assertEqual(m, mf.model);
    },

    modelstring: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('¬q')]);
        var m = mf.tryNextModel();
        m = mf.tryNextModel();
        m = mf.tryNextModel();
        var s = m.toString();
        assert(s.indexOf('true')>-1);
        assert(s.indexOf('false')>-1);
    },

    findmodel1: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('Fa ∧ ¬Fb')];
        var mf = new ModelFinder(fs);
        var m;
        for (var i=0; i<100; i++) {
            m = mf.tryNextModel();
            if (m) break;
        }
        assertEqual(m.domain.length, 2);
        assertEqual(m.satisfies([parser.parseFormula('Fa')]), true);
        assertEqual(m.satisfies([parser.parseFormula('Fb')]), false);
        console.log(m.toString());
    },

    findmodel2: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀x∃yRxy ∧ ¬∃xRxx')];
        fs = fs.map(function(f){return f.normalize()});
        var mf = new ModelFinder(fs);
        var m;
        for (var i=0; i<100; i++) {
            m = mf.tryNextModel();
            if (m) break;
        }
        console.log(m.toString());
        assertEqual(m.getValue('R',[0,1]), 1);
        assertEqual(m.getValue('R',[1,0]), 1);
        assertEqual(m.getValue('R',[0,0]), 0);
        assertEqual(m.getValue('R',[1,1]), 0);
    },

    findmodel_modal: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('□p→p')];
        fs = fs.map(function(f){return f.translateModal().normalize()});
        var mf = new ModelFinder(fs);
        var m;
        for (var i=0; i<100; i++) {
            m = mf.tryNextModel();
            if (m) break;
        }
        console.log(m.toString());
        assertEqual(m.worlds.length, 1);
        assertEqual(m.getValue('R',[0,0]), 0);
    },

    findmodel_modal2: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('◇p'), parser.parseFormula('¬p')];
        fs = fs.map(function(f){return f.translateModal().normalize()});
        var mf = new ModelFinder(fs);
        var m;
        for (var i=0; i<100; i++) {
            m = mf.tryNextModel();
            if (m) break;
        }
        console.log(m.toString());
        assertEqual(m.worlds.length, 1);
        assertEqual(m.getValue('R',[0,0]), 0);
    },

    findmodel3_TODO: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀y∃x(Ryx ∧ ¬Rxy)')]; // takes forever
        fs = fs.map(function(f){return f.normalize()});
        var mf = new ModelFinder(fs);
        var m;
        for (var i=0; i<10; i++) {
            m = mf.tryNextModel();
            if (m) break;
        }
        console.log(m.toString());
    },
    
    
}
