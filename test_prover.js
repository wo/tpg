
tests = {

    refutepandnotp: function() {
        var parser = new Parser();
        var f = parser.parseFormula('p∧¬p');
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length == 0);
    },

    prooftest2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∀x(Fx→Fx)').normalize();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length == 0);
    },

    prooftest3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∀x¬Ff(ab)').normalize(); // old prover says invalid and stops at the double negation!
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length > 0);
    },

    prooftest4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∃y∀x(Fy→Fx)').normalize();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length == 0);
    },


    modelfinder_setup: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('Ff(a,a)')]);
        assert(mf.constants.equals(['f','a']));
        assert(mf.predicates.equals(['p','F']));
        mf.model.initInterpretation(1);
        assertEqual(mf.model.domain.length, 1);
        assertEqual(mf.model.argLists.length, 3); // two arities (0, 1 and 2)
        assertEqual(mf.model.argLists[1].length, 1); // one possible argument list of length 1: '[0]'
        assertEqual(mf.model.argLists[1][0], '[0]');
        assertEqual(mf.model.argLists[2][0], '[0,0]'); // one possible argument list of length 2
        assertEqual(mf.model.values['p'], false);
        assertEqual(mf.model.values['a'], 0);
        assertEqual(mf.model.values['F'][0], false);
        assertEqual(mf.model.values['f'][0], 0);
        assertEqual(mf.model.getValue('p'), false);
        assertEqual(mf.model.getValue('F', [0]), false);
        assertEqual(mf.model.getValue('f', [0,0]), 0);
    },

    modelfinder_satisfies: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('Ff(a,b)')]);
        mf.model.initInterpretation(1);
        assertEqual(mf.model.satisfies(parser.parseFormula('p')), false);
        assertEqual(mf.model.satisfies(parser.parseFormula('¬p')), true);
        assertEqual(mf.model.satisfies(parser.parseFormula('Fa')), false);
        assertEqual(mf.model.satisfies(parser.parseFormula('Ff(a,b)')), false);
        assertEqual(mf.model.satisfies(parser.parseFormula('Ff(f(a,a),b)')), false);
    },

    modelfinder_iterate1: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p')]);
        assertEqual(mf.tryNextModel(), null);
        assert(mf.tryNextModel() != null);
    },
    
    modelfinder_iterate2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∃xFx')]);
        assertEqual(mf.tryNextModel(), null);
        assert(mf.tryNextModel() != null);
    },
    
    modelfinder_iterate3: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∃xFg(ab)')]);
        assertEqual(mf.tryNextModel(), null);
        assert(mf.tryNextModel() != null);
    }

}
