
tests = {

    refutepandnotp: function() {
        var parser = new Parser();
        var f = parser.parseFormula('p∧¬p');
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length == 0);
    },

    prooftest2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∀x(Fx→Fx)').normalize();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length == 0);
    },

    prooftest3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∀x¬Ff(ab)').normalize(); // old prover says invalid and stops at the double negation!
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length > 0);
    },

    prooftest4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∃y∀x(Fy→Fx)').normalize();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.openBranches.length, 0);
    },

    pruneBranch: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(¬R∧¬S∧((R∧¬S)∨(¬R∧S))∧(Q∨P))').normalize();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.closedBranches.length, 2);
    },
    
    
}
