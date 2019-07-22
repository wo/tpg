
tests = {

    atoa: function() {
        var f = new Parser().parseFormula('A→A').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, [f]);
        assertEqual(sentree.nodes.length, 3);
    },

    peirce: function() {
        var f = new Parser().parseFormula('((A→B)→A)→A').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, [f]);
        assertEqual(sentree.nodes.length, 7);
        assertEqual(sentree.nodes[2].children[1].formula.string, 'A');
    },
    
    dne: function() {
        var f = new Parser().parseFormula('¬((A∧¬A)∨(A∧¬A))').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, [f]);
        assertEqual(sentree.nodes.length, 8);
        assertEqual(sentree.nodes[0].children.length, 1);
    },
    
    bicondAndDn: function() {
        var f = new Parser().parseFormula('¬(A↔¬A)').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, [f]);
        assertEqual(sentree.nodes.length, 6);
        assertEqual(sentree.nodes[1].children[0].formula.string, 'A');
    },
    
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
    },
    
    model_from_tree: function() {
        var parser = new Parser();
        var f = parser.parseFormula('p→q').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentenceTree = new SenTree(prover.tree);
        var counterModel = sentenceTree.getCounterModel();
        assertEqual(counterModel.satisfies(parser.parseFormula('p')), true);
        assertEqual(counterModel.satisfies(parser.parseFormula('q')), false);
    },
    
    model_from_tree2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬(p→q)').negate();
        var prover = new Prover([f]);
        prover.pauseLength = 0;
        prover.start();
        var sentenceTree = new SenTree(prover.tree);
        var counterModel = sentenceTree.getCounterModel();
        assertEqual(counterModel.satisfies(parser.parseFormula('p')), false);
        assertEqual(counterModel.satisfies(parser.parseFormula('q')), true);
    }
    
}
