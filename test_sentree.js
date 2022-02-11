
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

    dne3: function() {
        // handle triply and quadruply negated formulas
        var parser = new Parser();
        var f = parser.parseFormula('¬¬¬∃x(Fx∧Gx)↔∀x¬(Fx∧Gx)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 21);
    },

    dne4: function() {
        // don't branch for DNE
        var parser = new Parser();
        var f = parser.parseFormula('¬∃x(Fx∧Gx)↔∀x¬(Fx∧Gx)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes[3].children.length, 1);
    },
    
    dne5: function() {
        // expand DNE nodes that are only needed for closing a branch (not in any fromNodes)
        var parser = new Parser();
        var f = parser.parseFormula('¬¬¬¬¬¬p→p').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 6);
    },
    
    dne6: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬¬¬¬((A↔A)↔(A↔¬¬¬¬A))').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 27);
    },
    
    bicondAndDn: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬(A↔¬A)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 7);
        assertEqual(sentree.nodes[0].children[0].children[0].formula.string, 'A');
    },

    emil: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇□A→(◇□B→◇□(A∧B))').negate();
        var prover = new Prover([f], parser, ['reflexivity', 'symmetry', 'transitivity']);
        prover.pauseLength = 0;
        prover.start();
        assertEqual(prover.tree.openBranches.length, 0);
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 19);
    },    
    
    nicenames: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∃y∀x(Fy→Fx)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes[1].formula.string, '¬∀x(Fa → Fx)');
        assertEqual(sentree.nodes[2].formula.string, '¬(Fa → Fb)');
    },

    catchSkolemTermsInFunctions: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∃xFf(x)→¬∀x¬F(x)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assert(sentree.toString().indexOf('Ff(a)')>0);
        assert(sentree.toString().indexOf('φ') == -1);
    },

    replaceSkolemTerms: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((∃x∀yRyx ∨ ∀x∀yByx) ∧ ∃x∀y(Cy→ ¬Byx))→∀x∃y(Cx→Rxy)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assert(sentree.toString().indexOf('φ') == -1);
    },

    replaceNestedSkolemTerms: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(∀x∃yCxy∧∀x∀y(Cxy→Cyx)∧∀x∀y∀z((Cxy∧Cyz)→Cxz))→∀xCxx').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentreeString = new SenTree(prover.tree, parser).toString();
        assert(sentreeString.indexOf('φ') == -1);
        // only need two constants; these should be 'a' and 'c':
        assert(sentreeString.indexOf('a') > 0);
        assert(sentreeString.indexOf('b') > 0);
        assert(sentreeString.match(/cdefgh/) == null);
    },

    removeUnusedBranches: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(∀x∀y∀z((Ixy→Iyz)→Ixz)∧((IaW(a)∧IbW(b))∧(∀x∀y∀z(Ixy→(IzW(x)→IzW(y)))∧¬Iba)))');
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assert(sentree.nodes.length <= 15);
    },

    github14qml: function() {
        var parser = new Parser();
        var f = parser.parseFormula('((∀x((Ox∧Mx)→(◇(Ox∧Px)∧◇(Ox∧¬Px)))∧∃x(Ox∧Mx))∧(∀x((Ox∧Mx)→(◇(Ox∧Sx)∧◇(Ox∧¬Sx)))∧∃x(Ox∧Mx)))→(∃x(◇(Ox∧Sx)∧◇(Ox∧¬Px))∨¬∃x◇(Ox∧Sx))').negate();
        var prover = new Prover([f], parser, ['universality']);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assert(sentree.nodes.length > 5);
    },

    rigididentity: function() {
        var parser = new Parser();
        var f = parser.parseFormula('a=b → □a=b').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assertEqual(sentree.nodes.length, 6);
    },

    rigididentity2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(□(□p→p)→□p)∧(□(□□p→□p)→□□p)∧(□(□¬□p→¬□p)→□¬□p)→(□p→□□p)').negate();
        var prover = new Prover([f], parser);
        prover.pauseLength = 0;
        prover.start();
        var sentree = new SenTree(prover.tree, parser);
        assert(sentree.nodes.length >= 30);
    }
        
    
    // getcountermodel: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('Fa').negate();
    //     var prover = new Prover([f], parser);
    //     prover.pauseLength = 0;
    //     prover.start();
    //     var sentree = new SenTree(prover.tree, parser);
    //     var m = sentree.getCounterModel();
    //     assertEqual(m.domain.length, 1);
    //     assert(m.toString().indexOf('a: 0') > 0);
    // },

    // getcountermodel2: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('Ff(ab)').negate();
    //     var prover = new Prover([f], parser);
    //     prover.pauseLength = 0;
    //     prover.start();
    //     var sentree = new SenTree(prover.tree, parser);
    //     var m = sentree.getCounterModel();
    //     assertEqual(m.domain.length, 3);
    // },
    
    // getcountermodel3: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('p→q').negate();
    //     var prover = new Prover([f], parser);
    //     prover.pauseLength = 0;
    //     prover.start();
    //     var sentenceTree = new SenTree(prover.tree, parser);
    //     var m = sentenceTree.getCounterModel();
    //     assert(m.toString().indexOf('p: true') >= 0);
    //     assert(m.toString().indexOf('q: false') >= 0);
    // },
    
    // getcountermodel4: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('¬(p→q)').negate();
    //     var prover = new Prover([f], parser);
    //     prover.pauseLength = 0;
    //     prover.start();
    //     var sentenceTree = new SenTree(prover.tree, parser);
    //     var m = sentenceTree.getCounterModel();
    //     assert(m.toString().indexOf('p: false') >= 0);
    //     assert(m.toString().indexOf('q: true') >= 0);
    // },
    
    // getcountermodelModal1: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('□p').negate();
    //     var prover = new Prover([f], parser);
    //     prover.pauseLength = 0;
    //     prover.start();
    //     var sentenceTree = new SenTree(prover.tree, parser);
    //     var m = sentenceTree.getCounterModel();
    //     assertEqual(m.worlds.length, 2)
    //     assert(m.toString().indexOf('R: { (w0,w1) }') >= 0);
    //     assert(m.toString().indexOf('p: {  }') >= 0);
    // },
    
    // getcountermodelModal2: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('◇p').negate();
    //     var prover = new Prover([f], parser);
    //     prover.pauseLength = 0;
    //     prover.start();
    //     var sentenceTree = new SenTree(prover.tree, parser);
    //     var m = sentenceTree.getCounterModel();
    //     assertEqual(m.worlds.length, 1)
    //     assert(m.toString().indexOf('R: {  }') >= 0);
    //     assert(m.toString().indexOf('p: {  }') >= 0);
    // },

    // getcountermodels5: function() {
    //     var parser = new Parser();
    //     var f = parser.parseFormula('□p').negate();
    //     var prover = new Prover([f], parser, ['universality']);
    //     prover.pauseLength = 0;
    //     prover.modelfinder.nextStep = function() { return false; };
    //     prover.start();
    //     var sentenceTree = new SenTree(prover.tree, parser);
    //     var m = sentenceTree.getCounterModel();
    //     assertEqual(m.worlds.length, 2)
    //     assert(m.toString().indexOf('R') == -1);
    //     assert(m.toString().indexOf('p: {  }') >= 0);
    // },
    
    
}
