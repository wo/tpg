
tests = {

    // Recall that Prover takes the /negated/ sentence that is to be proved
    // as input; i.e. Prover is really a Refuter.

    noRuleApplication: function() {
        var parser = new Parser();
        var f = parser.parseFormula('p');
        var prover = new Prover([f, f.negate()], parser);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.closedBranches.length, 1);
    },


    pruneBranch: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(¬R∧¬S∧((R∧¬S)∨(¬R∧S))∧(Q∨P))').normalize();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.closedBranches.length, 2);
    },

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
        var f = parser.parseFormula('∀x(Fx→Fx)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length == 0);
    },

    prooftest4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∃y∀x(Fy→Fx)');
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.openBranches.length, 0);
    },

    modalT: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p→p').negate();
        ['universality', 'reflexivity'].forEach(function(c) {
            var prover = new Prover([f], parser, [c]);
            prover.pauseLength = 0;
            prover.start();
            assertEqual(prover.tree.openBranches.length, 0);
            var numNodes = c == 'universality' ? 4 : 5;
            assertEqual(prover.tree.closedBranches[0].nodes.length, numNodes);
        });
        var prover = new Prover([f], parser, ['seriality']);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.openBranches.length, 1);
    },    

    modalG1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇□p→□◇p').negate();
        ['universality', 'euclidity'].forEach(function(c) {
            var prover = new Prover([f], parser, [c]);
            prover.pauseLength = 0;
            prover.start();
            assertEqual(prover.tree.openBranches.length, 0);
            var numNodes = c == 'universality' ? 7 : 14;
            assertEqual(prover.tree.closedBranches[0].nodes.length, numNodes);
        });
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.openBranches.length, 1);
    },

    // emil: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('◇□A→(◇□B→◇□(A∧B))').negate();
    //     var prover = new Prover([f], parser, ['reflexivity', 'symmetry', 'transitivity']);
    //     prover.pauseLength = 0;
    //     prover.start();
    //     assertEqual(prover.tree.openBranches.length, 0);
    // },    

    noSerialityLoop: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇(p∧□q)→◇(p∧◇q)').negate();
        var prover = new Prover([f], parser, ['seriality']);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.openBranches.length, 0);
    },

    invalidtest1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x¬Ff(ab)').negate(); // old prover says invalid and stops at the double negation!
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        assert(prover.tree.openBranches.length > 0);
    },

    s5_Fails_should_be_able_to_detect_infinite_tree: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇p').negate();
        var prover = new Prover([f], parser, ['universality']);
        prover.pauseLength = 0;
        prover.modelfinder.nextStep = function() { return false; };
        prover.onfinished = function(res) {
            assertEqual(res, 0);
            return true;
        }
        for (var i=0; i<100; i++) {
            prover.stopTimeout = true;
            if (prover.nextStep()) break;
        }
        assert(i<100);
    },
    
    
}
