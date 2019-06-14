
tests = {

    getcountermodel: function() {
        var f = new Parser().parseFormula('Fa').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, [f]);
        var m = sentree.getCounterModel();
        assertEqual(m.domain.length, 1);
        assertEqual(m.values['a'], 0);
    },

    getcountermodelfunc: function() {
        var f = new Parser().parseFormula('Ff(ab)').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, [f]);
        var m = sentree.getCounterModel();
        assertEqual(m.domain.length, 3);
    }

}
