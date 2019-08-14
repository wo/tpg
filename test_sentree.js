
tests = {

    atoa: function() {
        var parser = new Parser();
        var f = parser.parseFormula('A→A').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 3);
    },

    peirce: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((A→B)→A)→A').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 7);
        assertEqual(sentree.nodes[2].children[1].formula.string, 'A');
    },
    
    dne: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬((A∧¬A)∨(A∧¬A))').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 8);
        assertEqual(sentree.nodes[0].children.length, 1);
    },
    
    dne2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∀x(Fx∧∃y¬Fy)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 9);
    },
    
    bicondAndDn: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬(A↔¬A)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 6);
        assertEqual(sentree.nodes[1].children[0].formula.string, 'A');
    },

    getcountermodel: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Fa').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        var m = sentree.getCounterModel();
        assertEqual(m.domain.length, 1);
        assert(m.toString().indexOf('a: 0') > 0);
    },

    getcountermodel2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Ff(ab)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        var m = sentree.getCounterModel();
        assertEqual(m.domain.length, 3);
    },
    
    getcountermodel3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('p→q').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentenceTree = new SenTree(prover.tree, parser);
        var m = sentenceTree.getCounterModel();
        assert(m.toString().indexOf('p: true') >= 0);
        assert(m.toString().indexOf('q: false') >= 0);
    },
    
    getcountermodel4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬(p→q)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentenceTree = new SenTree(prover.tree, parser);
        var m = sentenceTree.getCounterModel();
        assert(m.toString().indexOf('p: false') >= 0);
        assert(m.toString().indexOf('q: true') >= 0);
    },
    
    getcountermodelModal1: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentenceTree = new SenTree(prover.tree, parser);
        var m = sentenceTree.getCounterModel();
        assertEqual(m.worlds.length, 2)
        assert(m.toString().indexOf('R: { (0,1) }') >= 0);
        assert(m.toString().indexOf('p: {  }') >= 0);
    },
    
    getcountermodelModal2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇p').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentenceTree = new SenTree(prover.tree, parser);
        var m = sentenceTree.getCounterModel();
        assertEqual(m.worlds.length, 1)
        assert(m.toString().indexOf('R: {  }') >= 0);
        assert(m.toString().indexOf('p: {  }') >= 0);
    },

    getcountermodels5: function() {
        var parser = new Parser();
        var f = parser.parseFormula('□p').negate();
        var prover = new Prover([f], parser, ['universality']);
        prover.pauseLength = 0;
        prover.modelfinder.nextStep = function() { return false; };
        prover.start();
        var sentenceTree = new SenTree(prover.tree, parser);
        var m = sentenceTree.getCounterModel();
        assertEqual(m.worlds.length, 2)
        assert(m.toString().indexOf('R') == -1);
        assert(m.toString().indexOf('p: {  }') >= 0);
    },
    
    
}
