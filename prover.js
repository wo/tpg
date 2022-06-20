function Prover(initFormulas, parser, accessibilityConstraints) {
    /**
     * A Prover object collects functions and properties used to find either a
     * tableau proof or a countermodel. <initFormulas> is the list of formulas
     * with which the tableau begins (all premises, if any, plus the negated
     * conclusion); <parser> is the Parser object used to parse these formulas;
     * <accessibilityConstraints> is a list of words like 'reflexivity'
     * determinining the relevant modal system.
     */

    log("*** initializing prover");

    parser = parser.copy();
    this.parser = parser;
    this.initFormulas = initFormulas; // formulas as entered, with conclusion negated
    this.initFormulasNonModal = initFormulas;
    this.accessibilityRules = [];
    if (parser.isModal) {
        // convert modal formulas into two-sorted first-order formulas:
        this.initFormulasNonModal = initFormulas.map(function(f) {
            return parser.translateFromModal(f);
        });
        if (accessibilityConstraints) {
            this.s5 = accessibilityConstraints.includes('universality');
            if (!this.s5) {
                this.accessibilityRules = accessibilityConstraints.map(function(s) {
                    return Prover[s];
                });
            }
        }
    }
    this.initFormulasNNF = this.initFormulasNonModal.map(function(f){
        return f.nnf();
    });
    // These are the formulas that we'll use on the internal tableaux.
    log('initFormulas in NNF: '+this.initFormulasNNF);
    
    // init tableau prover:
    this.pauseLength = 5; // ms pause between calculations
    log('increasing pauseLength to '+(this.pauseLength = 10));
    this.computationLength = 20; // ms before setTimeout pause
    this.step = 0; // counter of calculation steps
    this.tree = new Tree(this);
    this.depthLimit = 2; // how far to explore a tree before backtracking
    this.alternatives = [this.tree]; // alternative trees for backtracking
    this.curAlternativeIndex = 0;
    this.tree.addInitNodes(this.initFormulasNNF)

    // init modelfinder:
    log("initializing modelfinder")
    var mfParser = parser.copy();
    if (accessibilityConstraints) {
        var name2fla = {
            "universality": "∀v∀uRvu",
            "reflexivity": "∀vRvv",
            "symmetry": "∀v∀u(Rvu→Ruv)",
            "transitivity": "∀v∀u∀t(Rvu→(Rut→Rvt))",
            "euclidity": "∀v∀u∀t(Rvu→(Rvt→Rut))",
            "seriality": "∀v∃uRvu"
        };
        var accessibilityFormluas = accessibilityConstraints.map(function(s) {
            return mfParser.parseAccessibilityFormula(name2fla[s]).nnf();
        });
        // todo: strip redundant constraints
        this.modelfinder = new ModelFinder(
            this.initFormulasNNF,
            mfParser,
            accessibilityFormluas,
            this.s5
        );
    }
    else {
        this.modelfinder = new ModelFinder(this.initFormulasNNF, mfParser);
    }
    this.counterModel = null;

    this.start = function() {
        this.lastBreakTime = performance.now();
        this.nextStep();
    };

    this.stop = function() {
        this.stopTimeout = true;
    };

    this.onfinished = function(treeClosed) {}; // to be overwritten
    this.status = function(str) {}; // to be overwritten

}

Prover.prototype.nextStep = function() {
    /**
     * expand the next node on the left-most open branch; initializes
     * backtracking if limit is reached; also search for a countermodel. This
     * function calls itself again until the proof is complete.
     */
    this.step++;
    log('*** prover step '+this.step+' alternative '+this.curAlternativeIndex+' (max '+(this.alternatives.length-1)+')');
    log(this.tree);

    if (this.tree.openBranches.length == 0) {
        log('tree closed');
        return this.onfinished(1);
    }
    
    this.status('step '+this.step+' alternative '+this.curAlternativeIndex+', '
                +this.tree.numNodes+' nodes, model size '
                +this.modelfinder.model.domain.length
                +(this.tree.parser.isModal ? '/'+this.modelfinder.model.worlds.length : ''));

    if (this.limitReached()) {
        log(" * limit "+this.depthLimit+" reached");
        if (this.curAlternativeIndex < this.alternatives.length-1) {
            this.curAlternativeIndex++;
            log(" * trying stored alternative");
        }
        else {
            // this.depthLimit += Math.ceil(this.alternatives.length/20);
            this.depthLimit += 2 + Math.floor(this.step/500);
            this.curAlternativeIndex = 0;
            log(" * increasing to "+this.depthLimit);
        }
        this.tree = this.alternatives[this.curAlternativeIndex];
        return this.nextStep(); // need to check if alternative is also at limit
    }

    var todo = this.tree.openBranches[0].todoList.shift();
    if (todo) {
        todo.nextRule(this.tree.openBranches[0], todo.args);
    }
    else if (this.alternatives.length) {
        // If we reason with equality, todoList may be empty even though the tree isn't finished
        // because we consider trees without equality reasoning.
        log("nothing left to do");
        this.discardCurrentAlternative();
    }
    
    // search for a countermodel:
    if (this.modelfinder.nextStep()) {
        this.counterModel = this.modelfinder.model;
        return this.onfinished(0);
    }
    
    var timeSinceBreak = performance.now() - this.lastBreakTime;
    if (this.stopTimeout) {
        // proof manually interrupted
        this.stopTimeout = false;
    }
    else if (this.pauseLength && timeSinceBreak > this.computationLength) {
        // continue with next step after short break to display status message
        // and not get killed by browsers
        setTimeout(function(){
            this.lastBreakTime = performance.now();
            this.nextStep();
        }.bind(this), this.pauseLength+this.tree.numNodes/1000);
    }
    else {
        this.nextStep();
    }
}

Prover.prototype.limitReached = function() {
    /**
     * check if the current tree has been explored up to depthLimit
     */
    var complexity = this.tree.getNumNodes() - this.tree.priority;
    if (this.tree.openBranches[0].todoList[0] &&
        this.tree.openBranches[0].todoList[0].nextRule == Prover.equalityReasoner) {
        if (!this.equalityComputationStep) this.equalityComputationStep = 1;
        else if (++this.equalityComputationStep == 100) {
            this.equalityComputationStep = 0;
            return true;
        }
    }
    // complexity += this.curAlternativeIndex/100;
    return complexity >= this.depthLimit; 
}

Prover.prototype.useTree = function(tree, index) {
    /**
     * replace currently active tree alternative by <tree>; if <index> is given,
     * inserts <tree> at <index> in this.alternatives
     */
    if (index !== undefined) {
        this.alternatives.splice(index, 0, tree);
        this.curAlternativeIndex = index;
    }
    else {
        this.alternatives[this.curAlternativeIndex] = tree;
    }
    this.tree = tree
}

Prover.prototype.switchToAlternative = function(altTree) {
    /**
     * continue proof search with <altTree> (member of this.alternatives)
     */
    this.curAlternativeIndex = this.alternatives.indexOf(altTree);
    this.tree = this.alternatives[this.curAlternativeIndex];
}

Prover.prototype.storeAlternatives = function(altTrees) {
    /**
     * add <altTrees> as alternatives to be explored after the current tree;
     * remove redundant alternatives
     */
    log("storing "+altTrees.length+" alternatives");
    var insertPosition = this.curAlternativeIndex+1;
    for (var i=0; i<altTrees.length; i++) {
        this.alternatives.splice(insertPosition, 0, altTrees[i]);
        this.pruneAlternatives(altTrees[i]);
        if (!altTrees[i].removed) {
            insertPosition++;
        }
    }
    log("There are now "+this.alternatives.length+' alternatives');
    log(this.alternatives.map(function(t,i) { return "alternative "+i+":"+t }).join('<br>')); 
}

Prover.prototype.pruneAlternatives = function(tree) {
    /**
     * discard elements in this.alternatives that have become redundant after <tree>
     * has been added or altered; might remove <tree> itself if it is found redundant;
     * removed trees get attribute 'removed'
     */
    log("pruning alternatives");
    log("There are currently "+this.alternatives.length+' alternatives');
    log(this.alternatives.map(function(t,i) { return "alternative "+i+":"+t }).join('<br>')); 
    for (var i=0; i<this.alternatives.length; i++) {
        if (this.alternatives[i] == tree) continue;
        var keepWhich = this.keepWhichTree(tree, this.alternatives[i]);
        var keepTree = keepWhich[0];
        var keepAlt = keepWhich[1];
        if (!keepTree) {
            log("removing tree<br>"+tree+"<br>in favour of alternative<br>"+this.alternatives[i]);
            this.removeAlternative(this.alternatives.indexOf(tree));
            return;
        }
        else if (!keepAlt) {
            log("removing alternative<br>"+this.alternatives[i]+"<br>in favour of<br>"+tree);
            this.removeAlternative(i);
            i--;
        }
    }
}

Prover.prototype.keepWhichTree = function(tree, altTree) {
    /**
     * compare <tree> and <altTree> from this.alternatives for redundancy; return
     * [Boolean1, Boolean2], where Boolean1 indicates if <tree> should be kept and
     * Boolean2 if <altTree> should be kept
     */
    if (altTree.string == tree.string) {
        if (tree.openBranches[0].todoList[0].nextRule != altTree.openBranches[0].todoList[0].nextRule ||
            tree.openBranches[0].todoList[0].args != altTree.openBranches[0].todoList[0].args) {
            return [true, true];
        }
        else if (tree.numNodes < altTree.numNodes) {
            log('alternative has same open branches and is larger; removing');
            return [true, false];
        }
        else {
            log('tree has same open branches as alternative; removing');
            return [false, true];
        }
    }
    var treeDiff = this.treeDiff(tree, altTree);
    var treeHasUnmatchedBranches = treeDiff[0];
    var altTreeHasUnmatchedBranches = treeDiff[1];
    if (treeHasUnmatchedBranches && altTreeHasUnmatchedBranches) {
        return [true, true];
    }
    if (treeHasUnmatchedBranches) {
        log('tree has extra open branches compared to alternative; removing');
        return [false, true];
    }
    if (altTreeHasUnmatchedBranches) {
        log('alternative has extra open branches; removing');
        return [true, false];
    }
    // Each open branch on one tree is qualitatively identical to or an
    // extension of an open branch on the other.
    if (tree.openBranches.length > altTree.openBranches.length) {
        log('tree has extra open branches; removing');
        return [false, true];
    }
    if (altTree.openBranches.length > tree.openBranches.length) {
        log('alternative has extra open branches; removing');
        return [true, false];
    }
    // The trees have the same open branches. We check if one tree is more
    // developed. Careful: We may want to store alternative ways of expanding an
    // open branch, so the mere fact that a branch is longer on one tree doesn't
    // mean it is a continuation of the other.
    var treeNodes = tree.openBranches[0].nodes;
    var altTreeNodes = altTree.openBranches[0].nodes;
    if (altTreeNodes.length > treeNodes.length &&
        tree.openBranches[0].todoList[0].nextRule != Prover.equalityReasoner) {
        log('tree is less developed than alternative; removing it');
        return [false, true];
    }
    else if (treeNodes.length > altTreeNodes.length &&
             altTree.openBranches[0].todoList[0].nextRule != Prover.equalityReasoner) {
        log('tree is more developed than alternative; removing alternative');
        return [true, false];
    }
    else return [true, true];
}

Prover.prototype.treeDiff = function(tree1, tree2) {
    /**
     * compare open branches of <tree1> and <tree2>; return [Boolean1, Boolean2],
     * where Boolean1 indicates if <tree1> has a branch that doesn't "match" a
     * branch of <tree2> and conversely for Boolean2; two branches "match" if
     * they have the same formulas or one is an initial segment of the other
     */
    var tree1hasUnmatchedBranches = false;
    var tree2hasUnmatchedBranches = false;
    var tree2matchedBranchIds = [];
    TREE1BRANCHLOOP:
    for (var i=0; i<tree1.openBranches.length; i++) {
        var string1 = tree1.openBranches[i].string;
        for (var j=0; j<tree2.openBranches.length; j++) {
            var string2 = tree2.openBranches[j].string;
            if (string1.startsWith(string2) || string2.startsWith(string1)) {
                // branches i and j match
                tree2matchedBranchIds.push(j);
                continue TREE1BRANCHLOOP;
            }
        }
        // branch i doesn't match any branch on tree2
        tree1hasUnmatchedBranches = true;
        break;
    }
    TREE2BRANCHLOOP:
    for (var j=0; j<tree2.openBranches.length; j++) {
        if (tree2matchedBranchIds.includes(j)) continue;
        var string2 = tree2.openBranches[j].string;
        for (var i=0; i<tree1.openBranches.length; i++) {
            var string1 = tree1.openBranches[i].string;
            if (string1.startsWith(string2) || string2.startsWith(string1)) {
                // branches i and j match
                continue TREE2BRANCHLOOP;
            }
        }
        // branch j doesn't match any branch on tree1
        tree2hasUnmatchedBranches = true;
        break;
    }
    return [tree1hasUnmatchedBranches, tree2hasUnmatchedBranches];
}

Prover.prototype.removeAlternative = function(index) {
    /**
     * remove alternative at position <index> from this.alternatives
     */
    log("removing alternative "+index+" of "+this.alternatives.length);
    this.alternatives[index].removed = true;
    if (index == this.curAlternativeIndex) {
        this.discardCurrentAlternative();
    }
    else {
        this.alternatives.splice(index, 1);
        if (index < this.curAlternativeIndex) {
            this.curAlternativeIndex--;
        }
    }
}

Prover.prototype.discardCurrentAlternative = function() {
    /**
     * remove current tree from this.alternatives and move to next one
     */
    this.alternatives.splice(this.curAlternativeIndex, 1);
    if (this.curAlternativeIndex == this.alternatives.length) {
        this.curAlternativeIndex = 0;
    }
    log("discarding current alternative; switching to alternative "+this.curAlternativeIndex);
    if (this.alternatives.length) {
        // don't make this.tree undefined if there are no more alternatives
        this.tree = this.alternatives[this.curAlternativeIndex];
    }
}

/**
 * What follows are functions corresponding to individual tableau expansion steps.
 */

Prover.alpha = function(branch, nodeList) {
    /**
     * expand a conjunction-type node; <nodeList> is a list because some rules
     * apply to more than one node. Not the alpha rule, so here <nodeList> has
     * just one member.
     */
    log('alpha '+nodeList[0]);
    var node = nodeList[0];
    var subnode1 = new Node(node.formula.sub1, Prover.alpha, nodeList);
    var subnode2 = new Node(node.formula.sub2, Prover.alpha, nodeList);
    branch.addNode(subnode1, 'addEvenIfDuplicate');
    branch.addNode(subnode2, 'addEvenIfDuplicate');
    branch.tryClose(subnode1);
    if (!branch.closed) branch.tryClose(subnode2);
}
Prover.alpha.priority = 1;
Prover.alpha.toString = function() { return 'alpha' }

Prover.beta = function(branch, nodeList) {
    /**
     * expand a disjunction-type node
     */
    log('beta '+nodeList[0]);
    var node = nodeList[0];
    var newbranch = branch.copy();
    branch.tree.openBranches.unshift(newbranch);
    // try to tackle simpler branch first:
    var re = /[∧∨↔→∀∃□◇]/g;
    var complexity1 = (node.formula.sub1.string.match(re) || []).length;
    var complexity2 = (node.formula.sub2.string.match(re) || []).length;
    if (complexity2 < complexity1) { 
        var subnode1 = new Node(node.formula.sub1, Prover.beta, nodeList);
        var subnode2 = new Node(node.formula.sub2, Prover.beta, nodeList);
    }
    else {
        var subnode2 = new Node(node.formula.sub1, Prover.beta, nodeList);
        var subnode1 = new Node(node.formula.sub2, Prover.beta, nodeList);
    }
    branch.addNode(subnode1, 'addEvenIfDuplicate');
    newbranch.addNode(subnode2, 'addEvenIfDuplicate');
    branch.tryClose(subnode1, 'dontPruneAlternatives');
    newbranch.tryClose(subnode2);
}
Prover.beta.priority = 9;
Prover.beta.toString = function() { return 'beta' }

Prover.gamma = function(branch, nodeList, matrix) {
    /**
     * expand an ∀ type node; <matrix> is set when this is called from modalGamma
     * for S5 trees, see modalGamma() below.
     */
    log('gamma '+nodeList[0]);
    var fromModalGamma = (matrix != undefined);
    var node = nodeList[0];
    var newVariable = branch.newVariable(matrix);
    var matrix = matrix || node.formula.matrix;
    var newFormula = matrix.substitute(node.formula.variable, newVariable);
    var newNode = new Node(newFormula, Prover.gamma, nodeList);
    // NB: The last line sets fromRule to gamma even for s5 modalGamma nodes
    newNode.instanceTerm = newVariable; // used in sentree
    branch.addNode(newNode);
    branch.tryClose(newNode);
    // add application back onto todoList:
    if (!fromModalGamma && newNode.type != 'gamma') {
        // When expanding ∀x∀y∀zφ, we add ∀y∀zφ and ∀zφ to the branch, all of
        // which can be expanded again and again, leading to lots of useless
        // variations of φ. So we only add the outermost sentence back to the
        // list, and only after the innermost was expanded, so that we first
        // expand φ before expanding ∀x∀y∀zφ again.
        var outer = node;
        while (outer.fromRule == Prover.gamma) outer = outer.fromNodes[0];
        var priority = 9;
        branch.todoList.push(Prover.makeTodoItem(Prover.gamma, [outer], priority));
    }
}
Prover.gamma.priority = 7;
Prover.gamma.toString = function() { return 'gamma' }

Prover.modalGamma = function(branch, nodeList) {
    /**
     * expand a (translated) node of type □A
     *
     * □A and ¬◇A nodes are translated into ∀x(¬wRxvAx) and ∀x(¬wRx∨¬Ax). By the
     * standard gamma rule, these would be expanded to ¬wRξ7 ∨ Aξ7 or ¬wRξ7 ∨
     * ¬Aξ7. We don't want the resulting branches on the tree. See readme.org
     */
    log('modalGamma '+nodeList[0]);
    var node = nodeList[0];
    // add application back onto todoList:
    branch.todoList.push(Prover.makeTodoItem(Prover.modalGamma, nodeList));
    
    if (branch.tree.prover.s5) {
        // In S5, we still translate □A into ∀x(¬wRxvAx) rather than ∀xAx.
        // That's because the latter doesn't tell us at which world the formula
        // is evaluated ('w'), which makes it hard to translate back into
        // textbook tableaux. (Think about the tableau for ◇□A→□A.) But when we
        // expand the □A node, we ignore the accessibility clause. Instead, we
        // expand ∀x(¬wRx∨Ax) to Aξ1 and use the free-variable machinery.
        return Prover.gamma(branch, nodeList, node.formula.matrix.sub2);
    }

    var wRx = node.formula.matrix.sub1.sub;
    log('looking for '+wRx.predicate+wRx.terms[0]+'* nodes');
    // find wR* node for □A expansion:
    OUTERLOOP:
    for (var i=0; i<branch.literals.length; i++) {
        var wRy = branch.literals[i].formula;
        if (wRy.predicate == wRx.predicate && wRy.terms[0] == wRx.terms[0]) {
            log('found '+wRy);
            // check if <node> has already been expanded with this wR* node:
            for (var j=0; j<branch.nodes.length; j++) {
                if (branch.nodes[j].fromRule == Prover.modalGamma &&
                    branch.nodes[j].fromNodes[0] == node &&
                    branch.nodes[j].fromNodes[1] == branch.literals[i]) {
                    log('already used');
                    continue OUTERLOOP;
                }
            }
            // expand <node> with found wR*:
            var modalMatrix = node.formula.matrix.sub2;
            var v = wRy.terms[1];
            log('expanding: '+node.formula.variable+' => '+v);
            var newFormula = modalMatrix.substitute(node.formula.variable, v);
            var newNode = new Node(newFormula, Prover.modalGamma, [node, branch.literals[i]]);
            newNode.instanceTerm = v;
            if (branch.addNode(newNode)) {
                branch.tryClose(newNode);
                break;
            }
        }
    }
}
Prover.modalGamma.priority = 8;
Prover.modalGamma.toString = function() { return 'modalGamma' }
    
Prover.delta = function(branch, nodeList, matrix) {
    /**
     * expand an ∃ type node; <matrix> is set when this is called from modalDelta
     * for S5 trees, see modalDelta() below.
     */
    log('delta '+nodeList[0]);
    var node = nodeList[0];
    var fla = node.formula;
    // find skolem term:
    var funcSymbol = branch.tree.newFunctionSymbol(matrix);
    // It suffices to skolemize on variables contained in this formula. This
    // makes some proofs much faster by making some gamma applications
    // redundant. However, translation into sentence tableau then becomes almost
    // impossible, because here we need the missing gamma applications. Consider
    // ∀x(Fx & ∃y¬Fy).
    if (branch.freeVariables.length > 0) {
        if (branch.tree.prover.s5) {
            // branch.freeVariables contains world and individual variables
            var skolemTerm = branch.freeVariables.filter(function(v) {
                return v[0] == (matrix ? 'ζ' : 'ξ');
            });
        }
        else {
            var skolemTerm = branch.freeVariables.copy();
        }
        skolemTerm.unshift(funcSymbol);
    }
    else {
        var skolemTerm = funcSymbol;
    }
    var matrix = matrix || node.formula.matrix;
    var newFormula = matrix.substitute(node.formula.variable, skolemTerm);
    var newNode = new Node(newFormula, Prover.delta, nodeList);
    newNode.instanceTerm = skolemTerm;
    branch.addNode(newNode);
    branch.tryClose(newNode);
}
Prover.delta.priority = 2;
Prover.delta.toString = function() { return 'delta' }

Prover.modalDelta = function(branch, nodeList) {
    /**
     * expand a (translated) node of type ◇A
     */
    log('modalDelta '+nodeList[0]);
    var node = nodeList[0]; // a node of type ∃x(wRx∧Ax)
    if (branch.tree.prover.s5) {
        // In S5, we still translate ◇A into ∃x(wRx∧Ax) rather than ∃xAx. That's
        // because the latter doesn't tell us at which world the formula is
        // evaluated ('w'), which makes it hard to translate back into textbook
        // tableaux. (Think about the tableau for ◇□A→□A.) But when we expand
        // the ◇A node, we ignore the accessibility clause. Instead, we expand
        // ∃x(wRx∧Ax) to Aφ, where φ is a suitable skolem term, just like for
        // ordinary existential formulas.
        return Prover.delta(branch, nodeList, node.formula.matrix.sub2);
    }
    var fla = node.formula;
    // don't need skolem terms (see readme.org):
    var newWorldName = branch.tree.newWorldName();
    // The instance formula would be wRu∧Au. We immediately expand the
    // conjunction to conform to textbooks modal rules:
    var fla1 = node.formula.matrix.sub1.substitute(node.formula.variable, newWorldName);
    var fla2 = node.formula.matrix.sub2.substitute(node.formula.variable, newWorldName);
    var newNode1 = new Node(fla1, Prover.modalDelta, nodeList); // wRu
    var newNode2 = new Node(fla2, Prover.modalDelta, nodeList); // Au
    newNode2.instanceTerm = newWorldName;
    branch.addNode(newNode1);
    branch.addNode(newNode2);
    branch.tryClose(newNode2);
}
Prover.modalDelta.priority = 2;
Prover.modalDelta.toString = function() { return 'modalDelta' }

Prover.literal = function(branch, nodeList) {
    /**
     * check if <branch> can be closed by applying a substitution, involving the
     * newly added literal(s) <nodeList> as either the member of a complementary
     * pair or as a self-complementary node ¬(Φ=Φ); also schedule the equality
     * reasoner that tries to close the branch by calling LL* on any equality
     * problem that newly arises on the branch by the addition of <nodeList>.
     *
     * There may be several options for closing the branch, with different
     * substitutions. We need to try them all. It may also be better to not close
     * the branch at all and instead continue expanding nodes. So we collect all
     * possible unifiers, try the first and store alternative trees for later
     * exploration with backtracking.
     *
     * (Sometimes a branch can be closed both by unifying a complementary pair
     * and by turning a new node into a self-complementary node. For example,
     * if the branch contains g(f(x1)) = x1 and the new node is ¬(x2=a), we can
     * unify the two formulas with x1->a, x2->g(f(a)), but we can also close the
     * branch by solving the trivial equality problem [] |- x2=a, whose solution
     * is x2->a.)
     *
     * (Why have a special rule/step for this, rather than calling it from
     * tryClose, in the same step in which the new node is added? Because we
     * would then create the relevant EqualityProblems on non-active branches
     * of a beta expansion. By the time we get to work on them, those
     * branches might have changed by applying a substitution that closed
     * the earlier active branch. As a result the created EqualityProblems
     * could involve equations or terms that are no longer on the branch.)
     */

    var tree = branch.tree;
    var prover = tree.prover;

    // collect unifiers that would allow closing the branch:
    var unifiers = [];
    for (var i=0; i<nodeList.length; i++) {
        unifiers.extendNoDuplicates(branch.getClosingUnifiers(nodeList[i]));
    }
    // We apply each unifier to a different copy of the present tree. If one
    // of them closes the entire tree, we're done. If not, and if there's a
    // unifier that doesn't affect other branches, we use that one and
    // discard the other tree copies. Otherwise we store the other copies
    // for backtracking.
    var altTrees = [];
    var localTree = null;
    for (var i=0; i<unifiers.length; i++) {
        log("processing unifier on new tree: "+unifiers[i]);
        var altTree = tree.copy();
        altTree.applySubstitution(unifiers[i]);
        altTree.closeCloseableBranches();
        if (altTree.openBranches.length == 0) {
            log('tree closes, stopping proof search');
            prover.useTree(altTree);
            return;
        }
        if (!localTree) {
            if (!branch.unifierAffectsOtherBranches(unifiers[i])) {
                log("That unifier didn't affect other branches.");
                localTree = altTree;
            }
            else {
                altTrees.push(altTree);
            }
        }
    }
    if (localTree) {
        log("continuing with unifier that doesn't affect other branches");
        prover.useTree(localTree);
        prover.pruneAlternatives(localTree);
        return;
    }

    // Instead of unifying (often as the only option), we could apply some other
    // rule. In particular, we could try to close the branch with an equality
    // rule.
    if (tree.parser.hasEquality) {
        log("checking if we could apply equality reasoning (on original tree)");
        var eqProbs = branch.createEqualityProblems(nodeList);
        if (eqProbs.length) {
            log("scheduling equality problem(s) (on a new tree): "+eqProbs);
            var altTree = tree.copy();
            altTree.openBranches[0].todoList = eqProbs.map(function(p) {
                return Prover.makeTodoItem(Prover.equalityReasoner, p);
            });
            // We erase the other todoList items: if the branch can't be closed
            // using equality reasoning, we'll switch to the alternative introduced
            // below
            altTrees.push(altTree);
        }
    }

    // Alternatively, we could apply an ordinary rule. (This is an alternative
    // to trying equality reasoning because the latter may only stop when
    // depthLimit is reached, in which case we want to switch to the alternative
    // of applying ordinary rules.)
    if (!altTrees.length) {
        // no alternatives found; simply continue with present tree
        return;
    }
    else if (branch.todoList.length) {
        log("unifier applied on new tree; saving original tree as alternative");
        altTrees.push(tree);
        // Now altTrees contains trees with a unifier applied, and, after those,
        // the original ununified tree.
    }
    // We continue with the first altTree and store the others for backtracking.
    var curTreeIndex = prover.curAlternativeIndex;
    // Delete the active element #curTreeIndex:
    prover.alternatives.splice(curTreeIndex, 1);
    if (altTrees.length) {
        do {
            log("switching to first of the just saved alternatives (if not redundant)");
            var newTree = altTrees.shift();
            // replaces prover.alternatives[curTreeIndex] with newTree:
            prover.useTree(newTree, curTreeIndex);
            prover.pruneAlternatives(newTree);
        } while (newTree.removed && altTrees.length);
        if (altTrees.length) {
            log("storing the others in prover.alternatives");
            prover.storeAlternatives(altTrees);
        }
    }
}
Prover.literal.priority = 0;
Prover.literal.toString = function() { return 'literal' };

Prover.equalityReasoner = function(branch, equalityProblem) {
    /**
     * expand the <EqualityProblem> by one RBS rule (roughly, one appliation of LL)
     *
     * This method follows a similar logic to Prover.literal.
     */

    log('tackling equality problem '+equalityProblem);

    // equalityProblem.nextStep returns a list of EqualityProblems beginning
    // with solved problems (if any) and continuing with problems that have
    // extended the original problem by zero or one application of (LL*).
    var newProblems = equalityProblem.nextStep();
    log("equality reasoning returned "+newProblems);

    if (newProblems.length == 0) {
        log("equalityProblem exhausted; no further rules to schedule");
        if (!branch.todoList[0]) {
            // We've already saved an alternative on which we continue with the
            // rest of the todoList (in literal()); so we can discard the
            // present alternative.
            branch.tree.prover.discardCurrentAlternative();
        }
        return;
    }

    // We apply each solution to a copy of the present tree. On all these copies,
    // the current branch gets closed. If one of them closes all branches, we're
    // done. Otherwise we continue with a solution that doesn't affect other
    // branches, if any. If there's none, we add all possibilities as alternatives
    // for backtracking.  (Note that when we copy the tree, we change the
    // identity of its Nodes, so the node references in newProblems break. We
    // fix this in branch.closeWithEquality().)
    var tree = branch.tree;
    var prover = tree.prover;
    var altTrees = [];
    var localTree = null;
    while (newProblems.length && !newProblems[0].nextStep) {
        // newProblems[0] is a solved problem (that closes the current branch)
        var solution = newProblems.shift();
        var substitution = solution.getSubstitution();
        // We could enforce a check that the solution makes use of newly added
        // equalities, but in tests this doesn't speed things up.
        log("applying solution "+solution);
        var altTree = tree.copy();
        altTree.openBranches[0].closeWithEquality(solution);
        altTree.closeCloseableBranches();
        if (altTree.openBranches.length == 0) {
            log('that tree closes, stopping proof search');
            prover.useTree(altTree);
            return;
        }
        if (!localTree) {
            if (!branch.unifierAffectsOtherBranches(substitution)) {
                localTree = altTree;
            }
            else {
                altTrees.push(altTree);
            }
        }
    }
    if (localTree) {
        log("continuing with solution that doesn't affect other branches");
        prover.useTree(localTree);
        prover.pruneAlternatives(localTree);
        return;
    }

    // We also consider the option of continuing with unsolved EqualityProblems
    // in order to find another solution (using the current tree)
    if (newProblems.length) {
        log("scheduling revised non-solution problems");
        var newTasks = newProblems.map(function(p) {
            return Prover.makeTodoItem(Prover.equalityReasoner, p);
        });
        branch.todoList.extend(newTasks);
        // Note that a substitution is only applied to this branch when the
        // branch is closed. So we don't need to worry about the terms and
        // equations of the new problems changing by the time we get to deal
        // with them at the end of the todoList. However, we do need to worry
        // about the fact that in-between rules might copy the present tree and
        // store it as an alternative. A copied tree has new Node objects, and
        // we need to make sure that the EqualityProblems on its todoLists point
        // to these Nodes. We do this in tree.copy().
    }

    if (!altTrees.length) {
        // no alternatives found; simply continue with present tree
        return;
    }
    else if (branch.todoList.length) {
        altTrees.push(tree);
    }
    // We continue with the first altTree and store the others for backtracking.
    var curTreeIndex = prover.curAlternativeIndex;
    prover.alternatives.splice(curTreeIndex, 1);
    if (altTrees.length) {
        do {
            log("switching to first alternative");
            var newTree = altTrees.shift();
            prover.useTree(newTree, curTreeIndex);
            prover.pruneAlternatives(newTree);
        } while (newTree.removed && altTrees.length);
        if (altTrees.length) {
            prover.storeAlternatives(altTrees);
        }
    }
}
Prover.equalityReasoner.priority = 0;
Prover.equalityReasoner.toString = function() { return 'equality' }

Prover.reflexivity = function(branch, nodeList) {
    /**
     * apply the modal reflexivity rule (add a wRw node); nodeList is either
     * empty or contains a node of form wRv where v might have been newly
     * introduced
     */
    log('applying reflexivity rule');
    if (nodeList.length == 0) {
        // rule applied to initial world w:
        var worldName = branch.tree.parser.w;
    }
    else {
        var worldName = nodeList[0].formula.terms[1];
    }
    var R = branch.tree.parser.R;
    var formula = new AtomicFormula(R, [worldName, worldName]);
    log('adding '+formula);
    var newNode = new Node(formula, Prover.reflexivity, nodeList || []);
    branch.addNode(newNode);
    // No point calling branch.tryClose(newNode): ~Rwv won't be on the branch.
}
Prover.reflexivity.priority = 3;
Prover.reflexivity.needsPremise = false; // can only be applied if wRv is on the branch
Prover.reflexivity.premiseCanBeReflexive = false; // can be applied to wRw
Prover.reflexivity.toString = function() { return 'reflexivity' }
    
Prover.symmetry = function(branch, nodeList) {
    /**
     * apply the modal symmetry rule (add vRw if wRv is on branch);
     * <nodeList> contains a node of form wRv
     */
    log('applying symmetry rule');
    var nodeFormula = nodeList[0].formula;
    var R = branch.tree.parser.R;
    var formula = new AtomicFormula(R, [nodeFormula.terms[1], nodeFormula.terms[0]]);
    log('adding '+formula);
    var newNode = new Node(formula, Prover.symmetry, nodeList);
    branch.addNode(newNode);
}
Prover.symmetry.priority = 3;
Prover.symmetry.needsPremise = true; // can only be applied if wRv is on the branch
Prover.symmetry.premiseCanBeReflexive = false; // can be applied to wRw
Prover.symmetry.toString = function() { return 'symmetry' }

Prover.euclidity = function(branch, nodeList) {
    /**
     * apply the modal euclidity rule (add vRu if wRv and wRu are on branch);
     * <nodeList> contains a newly added node of form wRv
     */
    log('applying euclidity rule');
    var node = nodeList[0];
    var nodeFla = node.formula;
    // When a wRv node has been added, euclidity always allows us to add vRv. In
    // addition, for each earlier wRu node, we can add uRv as well as
    // vRu. However, if we add all of these at once, they will be marked as
    // having been added in the same step, so that if some of them are
    // eventually used to derive a contradiction, senTree.removeUnusedNodes will
    // keep them all (ex.: ◇□p→□◇p). So we have to add them one by one. (And
    // they really are different applications of the euclidity rule.)
    var flaStrings = branch.nodes.map(function(n) {
        return n.formula.string;
    });
    var R = branch.tree.parser.R;
    for (var i=0; i<branch.nodes.length; i++) {
        var earlierFla = branch.nodes[i].formula;
        if (earlierFla.predicate != R) continue;
        if (earlierFla.terms[0] == nodeFla.terms[0]) {
            // earlierFla is wRu, nodeFla wRv (or earlierFla == nodeFla); need
            // to add uRv and vRu if not already there.
            var newFla;
            if (!flaStrings.includes(R + earlierFla.terms[1] + nodeFla.terms[1])) {
                newFla = new AtomicFormula(R, [earlierFla.terms[1], nodeFla.terms[1]]);
            }
            else if (!flaStrings.includes(R + nodeFla.terms[1] + earlierFla.terms[1])) {
                newFla = new AtomicFormula(R, [nodeFla.terms[1], earlierFla.terms[1]]);
            }
            if (newFla) {
                log('adding '+newFla);
                var newNode = new Node(newFla, Prover.euclidity, [branch.nodes[i], node]);
                if (branch.addNode(newNode)) {
                    branch.todoList.unshift(Prover.makeTodoItem(Prover.euclidity, nodeList, 0));
                    return;
                }
            }
        }
        if (branch.nodes[i] == node) break;
    }
}
Prover.euclidity.priority = 3;
Prover.euclidity.needsPremise = true; // can only be applied if wRv is on the branch
Prover.euclidity.premiseCanBeReflexive = true; // can be applied to wRw
Prover.euclidity.toString = function() { return 'euclidity' }

Prover.transitivity = function(branch, nodeList) {
    /**
     * apply the modal transitivity rule (add vRu if wRv and vRu are on branch);
     * <nodeList> contains a newly added node of form wRv
     */
    log('applying transitivity rule');
    var R = branch.tree.parser.R;
    var node = nodeList[0];
    var nodeFla = node.formula;
    // see if we can apply transitivity:
    for (var i=0; i<branch.nodes.length; i++) {
        var earlierFla = branch.nodes[i].formula;
        if (earlierFla.predicate != R) continue;
        var newFla = null;
        if (earlierFla.terms[1] == nodeFla.terms[0]) {
            // earlierFla uRw, nodeFla wRv
            newFla = new AtomicFormula(R, [earlierFla.terms[0], nodeFla.terms[1]]);
        }
        else if (earlierFla.terms[0] == nodeFla.terms[1]) {
            // earlierFla vRu, nodeFla wRv
            newFla = new AtomicFormula(R, [nodeFla.terms[0], earlierFla.terms[1]]);
        }
        if (newFla) {
            log('matches '+earlierFla+': adding '+newFla);
            var newNode = new Node(newFla, Prover.transitivity, [branch.nodes[i], node]);
            if (branch.addNode(newNode)) {
                branch.todoList.unshift(Prover.makeTodoItem(Prover.transitivity, nodeList, 0));
                return;
            }
        }
        if (branch.nodes[i] == node) break;
    }
}
Prover.transitivity.priority = 3;
Prover.transitivity.needsPremise = true; // can only be applied if wRv is on the branch
Prover.transitivity.premiseCanBeReflexive = false; // can be applied to wRw
Prover.transitivity.toString = function() { return 'transitivity' }

Prover.seriality = function(branch, nodeList) {
    /**
     * apply the modal seriality rule (add wRv); <nodeList> is either empty or
     * contains a newly added node of form wRv
     */
    log('applying seriality rule');
    var R = branch.tree.parser.R;
    if (nodeList.length == 0) {
        // rule applied to initial world w.
        var oldWorld = branch.tree.parser.w;
    }
    else {
        var oldWorld = nodeList[0].formula.terms[1];
    } 
    // check if oldWorld can already see a world:
    for (var i=0; i<branch.nodes.length-1; i++) {
        var earlierFla = branch.nodes[i].formula;
        if (earlierFla.predicate == R && earlierFla.terms[0] == oldWorld) {
            log(oldWorld+' can already see a world');
            return;
        }
    }
    var newWorld = branch.tree.newWorldName();
    var newFla = new AtomicFormula(R, [oldWorld, newWorld]);
    log('adding '+newFla);
    var newNode = new Node(newFla, Prover.seriality, []);
    branch.addNode(newNode);
}
Prover.seriality.priority = 10;
Prover.seriality.needsPremise = false; // can only be applied if wRv is on the branch
Prover.seriality.premiseCanBeReflexive = false; // can be applied to wRw
Prover.seriality.toString = function() { return 'seriality' }

Prover.makeTodoItem = function(nextRule, args, priority) {
    return {
        nextRule: nextRule,
        priority: priority || nextRule.priority,
        args: args
    }
}

function Tree(prover) {
    /**
     * a (partial) tableau
     */
    if (!prover) return; // for copy() function
    this.prover = prover;
    this.parser = prover.parser;
    this.openBranches = [new Branch(this)];
    this.closedBranches = [];
    this.numNodes = 0;
    this.skolemSymbols = []; // the function symbols used for skolem terms on the tree
    this.string = ""; // a string representation of the open branches, used in pruneAlternatives
    this.priority = 0;
}

Tree.prototype.addInitNodes = function(initFormulasNNF) {
    var initBranch = this.openBranches[0];
    for (var i=0; i<initFormulasNNF.length; i++) {
        var node = new Node(initFormulasNNF[i]);
        initBranch.addNode(node);
        initBranch.tryClose(node);
    }
}

Tree.prototype.closeBranch = function(branch, complementary1, complementary2) {
    /**
     * close branch <branch>; mark nodes as "used" for deriving the supplied
     * complementary pair
     */
    log('closing branch '+branch)
    branch.closed = true;
    branch.todoList = [];
    this.markUsedNodes(branch, complementary1, complementary2);
    this.openBranches.remove(branch);
    this.closedBranches.push(branch);
    log(this);
    this.pruneBranch(branch, complementary1, complementary2);
    this.string = this.openBranches.map(function(b) { return b.string }).join('|');
    var priorityBoost = Math.min(1, (this.numNodes-this.priority)/40);
    this.priority += priorityBoost*Math.max(1, 4-this.openBranches.length);
    log(this);
}

Tree.prototype.markUsedNodes = function(branch, complementary1, complementary2) {
    /**
     * add <branch>.id to node.used for all nodes that were involved in deriving
     * the supplied complementary pair
     */
    var ancestors = [complementary1, complementary2];
    var n;
    while ((n = ancestors.shift())) {
        // n is in the fromNodes chain of the complementary pair
        if (n.used.indexOf(branch.id) == -1) {
            n.used += branch.id;
            for (var i=0; i<n.fromNodes.length; i++) {
                ancestors.push(n.fromNodes[i]);
            }
        }
    }
}

Tree.prototype.pruneBranch = function(branch, complementary1, complementary2) {
    /**
     * remove redundant branches from current tree after <branch> has been
     * closed with the supplied complementary nodes
     * 
     * When a branch is closed, we look for branching steps that weren't used to
     * derive the complementary pair; we undo these steps and remove the other
     * branches originating from them.
     *
     * Example:
     *
     *           /-B--    can be removed (no matter if it's open or closed)
     * --Z--(AvB)       
     *           \-A-¬Z   x (AvB unused)
     *
     * A more tricky case:
     *
     *                        /-D--   
     *           /-B-----(CvD)
     * --Z--(AvB)             \-C-¬Z   x (AvB unused, CvD used)
     *           \-A---
     *
     * If the branch with D is closed (without using B), the A branch can be
     * removed (no matter if it's open or closed). But if the D branch is open,
     * the so-far unused node B may be needed to close that branch; so we have
     * to keep the AvB expansion. (It will be removed if the B node is not used
     * when closing the D branch.)
     *
     * Our general strategy is to walk up from the endpoint of the closed branch
     * until we reach a used branching node from which another open branch
     * emerges; any unused branching up to that point is removed.
     */
   
    var obranches = this.openBranches.concat(this.closedBranches);
    obranches.remove(branch);
    for (var i=branch.nodes.length-1; i>0; i--) {
        for (var j=0; j<obranches.length; j++) {
            if (obranches[j].nodes[i] &&
                obranches[j].nodes[i] != branch.nodes[i] &&
                obranches[j].nodes[i].expansionStep == branch.nodes[i].expansionStep) {
                // branch.nodes[i] is the result of a branching step;
                // obranches[j].nodes[i] is one if its siblings.
                if (branch.nodes[i].used) {
                    // quit if sibling branch is open:
                    if (!obranches[j].closed) return;
                }
                else {
                    log("pruning branch "+obranches[j]+": unused expansion of "+branch.nodes[i].fromNodes[0]);
                    if (obranches[j].closed) {
                        this.closedBranches.remove(obranches[j]);
                        // We need to remove 'used' marks from all remaining
                        // nodes that were only used to close the removed branch
                        // (including branch.nodes[i].fromNodes[0], but possibly
                        // other nodes as well, e.g. in the tree for
                        // ¬(∀x∀y∀z((Ixy→Iyz)→Ixz)∧((IaW(a)∧IbW(b))∧(∀x∀y∀z(Ixy→(IzW(x)→IzW(y)))∧¬Iba)));
                        // this is why we keep track of the branches for which a node is used.)
                        for (var k=0; k<i; k++) {
                            branch.nodes[k].used = branch.nodes[k].used.replace(obranches[j].id, '');
                        }
                    }
                    else {
                        this.openBranches.remove(obranches[j]);
                        obranches[j].removed = true; // for loop in closeCloseableBranches
                    }
                    this.numNodes -= (obranches[j].nodes.length - i);
                    log(this);
                    // We don't remove the beta expansion result on this branch;
                    // it'll be removed in the displayed sentence tree because
                    // it has .used == false
                }
            }
        }
        if (!this.nodeIsUsed(branch.nodes[i])) {
            this.removeNode(branch, i);
        }
    }
}

Tree.prototype.nodeIsUsed = function(node) {
    /**
     * check if <node> is used to close a branch on the tree, or is part of an
     * expansion that is used to close a branch
     */
    if (node.used) return true;
    var branches = this.openBranches.concat(this.closedBranches);
    for (var i=0; i<branches.length; i++) {
        for (var j=0; j<branches[i].nodes.length; j++) {
            if (branches[i].nodes[j].expansionStep == node.expansionStep
                && branches[i].nodes[j].used) {
                return true;
            }
        }
    }
    return false;
}

Tree.prototype.removeNode = function(branch, index) {
    /**
     * remove node with index <index> on branch <branch> from this tree
     */
    log("removing node "+branch.nodes[index]);
    var node = branch.nodes[index];
    var branches = this.openBranches.concat(this.closedBranches);
    for (var i=0; i<branches.length; i++) {
        if (branches[i].nodes[index] == node) {
            branches[i].nodes.splice(index,1);
        }
        if (node.type == 'literal') {
            branches[i].literals.remove(node);
        }
    }
    this.numNodes--;
}

Tree.prototype.closeCloseableBranches = function() {
    /**
     * close all branches on <tree> that can be closed without unification
     */
    log('checking for branches that can be closed without unification');
    var openBranches = this.openBranches.copy();
    var numOpenBranches = openBranches.length;
    for (var k=0; k<openBranches.length; k++) {
        var branch = openBranches[k];
        if (branch.removed) continue;
        // log('?b: '+branch);
        N1LOOP:
        for (var i=branch.nodes.length-1; i>=0; i--) {
            var n1 = branch.nodes[i];
            if (n1.formula.sub && n1.formula.sub.predicate == '='
                && [n1.formula.sub.terms[0]].equals([n1.formula.sub.terms[1]])) {
                this.closeBranch(branch, n1, n1);
                break N1LOOP;
            }
            var n1negated = (n1.formula.operator == '¬');
            for (var j=i-1; j>=0; j--) {
                var n2 = branch.nodes[j];
                // log('? '+n1+' '+n2);
                if (n2.formula.operator == '¬') {
                    if (n2.formula.sub.equals(n1.formula)) {
                        // log("+++ branch closed +++");
                        this.closeBranch(branch, n1, n2);
                        break N1LOOP;
                    }
                }
                else if (n1negated && n1.formula.sub.equals(n2.formula)) {
                    // log("+++ branch closed +++");
                    this.closeBranch(branch, n1, n2);
                    break N1LOOP;
                }
            }
        }
    }
}

Tree.prototype.getNumNodes = function() {
    /**
     * return the number of nodes on the current tree, including LL nodes
     * only registered in an EqualityProblem
     */
    try {
        return this.openBranches[0].todoList[0].args.newNodes.length +
            this.numNodes;
    }
    catch {
        return this.numNodes;
    }
}

Tree.prototype.copy = function() {
    /**
     * return a deep copy of this tree, including copies of the nodes
     * (but not of formulas)
     */
    var ntree = new Tree();
    var nodemap = {} // old node id => copied Node
    ntree.prover = this.prover;
    ntree.parser = this.parser;
    ntree.numNodes = this.numNodes;
    ntree.skolemSymbols = this.skolemSymbols.copy();
    ntree.openBranches = [];
    for (var i=0; i<this.openBranches.length; i++) {
        ntree.openBranches.push(copyBranch(this.openBranches[i]));
    }
    ntree.closedBranches = [];
    for (var i=0; i<this.closedBranches.length; i++) {
        ntree.closedBranches.push(copyBranch(this.closedBranches[i]));
    }
    ntree.string = this.string;
    ntree.priority = this.priority;
    return ntree;
    
    function copyBranch(orig) {
        var nodes = [];
        var literals = [];
        var todoList = [];
        for (var i=0; i<orig.nodes.length; i++) {
            nodes.push(copyNode(orig.nodes[i]));
        } 
        for (var i=0; i<orig.literals.length; i++) {
            literals.push(nodemap[orig.literals[i].id]);
        }
        for (var i=0; i<orig.todoList.length; i++) {
            var todo = {
                nextRule: orig.todoList[i].nextRule,
                priority: orig.todoList[i].priority
            };
            if (orig.todoList[i].args.equations) { // equalityProblem
                var eqProb = orig.todoList[i].args.copy();
                eqProb.terms1Node = nodemap[eqProb.terms1Node.id];
                eqProb.terms2Node = nodemap[eqProb.terms2Node.id];
                eqProb.equations = eqProb.equations.map(function(n){ return nodemap[n.id] });  
                todo.args = eqProb;
            }
            else {
                todo.args = orig.todoList[i].args.map(function(n) { return nodemap[n.id] });
            }
            todoList.push(todo);
        } 
        var b = new Branch(ntree, nodes, literals,
                           orig.freeVariables.copy(),
                           todoList, orig.closed);
        b.id = orig.id;
        b.string = orig.string;
        return b;
    }
    
    function copyNode(orig) { 
        if (nodemap[orig.id]) return nodemap[orig.id];
        var n = new Node();
        n.formula = orig.formula;
        n.fromRule = orig.fromRule;
        n.fromNodes = [];
        for (var i=0; i<orig.fromNodes.length; i++) {
            n.fromNodes.push(nodemap[orig.fromNodes[i].id]);
        }
        n.type = orig.type;
        n.expansionStep = orig.expansionStep;
        n.used = orig.used;
        n.id = orig.id;
        n.instanceTerm = orig.instanceTerm;
        nodemap[orig.id] = n;
        return n;
    }
    
}

Tree.prototype.applySubstitution = function(sub) {
    /**
     * apply substitution <sub> of terms for variables to all nodes on the tree
     */
    var branches = this.openBranches.concat(this.closedBranches);
    // (need to process closed branches so that displayed tree looks right)
    for (var i=0; i<sub.length; i+=2) {
        var nodeProcessed = {};
        for (var b=0; b<branches.length; b++) {
            for (var n=branches[b].nodes.length-1; n>=0; n--) {
                var node = branches[b].nodes[n]; 
                if (nodeProcessed[node.id]) break;
                node.formula = node.formula.substitute(sub[i], sub[i+1]);
                if (node.instanceTerm) {
                    node.instanceTerm = Formula.substituteInTerm(node.instanceTerm, sub[i], sub[i+1]);
                }
                nodeProcessed[node.id] = true;                    
            }
            branches[b].freeVariables.remove(sub[i]);
        }
    }
    for (var b=0; b<this.openBranches.length; b++) {
        this.openBranches[b].string = this.openBranches[b].nodes.map(function(n){
            return n.formula.string
        }).join(',');
    }
    this.string = this.openBranches.map(function(b) { return b.string }).join('|');
    // NB: substitution is also applied to EqualityProblems in branch.todoLists,
    // because these refer to nodes on the tree.
}

Tree.prototype.newFunctionSymbol = function(isWorldTerm) {
    /**
     * return new constant/function symbol for delta expansion
     */
    var sym = isWorldTerm ? 'ω' : 'φ';
    var res = sym+'1';
    for (var i=this.skolemSymbols.length-1; i>=0; i--) {
        if (this.skolemSymbols[i][0] == sym) {
            res = sym+(this.skolemSymbols[i].substr(1)*1+1);
            break;
        }
    }
    this.skolemSymbols.push(res);
    return res;
}

Tree.prototype.newWorldName = function() {
    return this.newFunctionSymbol(true);
}

Tree.prototype.toString = function() {
    for (var i=0; i<this.closedBranches.length; i++) {
        this.closedBranches[i].nodes[this.closedBranches[i].nodes.length-1].__markClosed = true;
    }
    var branches = this.closedBranches.concat(this.openBranches);
    var res = "<table><tr><td align='center' style='font-family:monospace'>" +
        getTree(branches[0].nodes[0])+"</td</tr></table>";
    for (var i=0; i<this.closedBranches.length; i++) {
        delete this.closedBranches[i].nodes[this.closedBranches[i].nodes.length-1].__markClosed;
    }
    res += "  todo: "+(this.openBranches[0] && this.openBranches[0].todoList.map(function(t) {
        return Object.values(t); }).join(', '))+"<br>";
    res += "  search depth: "+this.getNumNodes()+"-"+this.priority+"<br>";
    return res;
    
    function getTree(node) { 
        var recursionDepth = arguments[1] || 0;
        if (++recursionDepth > 100) return "<b>...<br>[max recursion]</b>";
        var children = [];
        for (var i=0; i<branches.length; i++) {
            for (var j=0; j<branches[i].nodes.length; j++) {
                if (branches[i].nodes[j-1] != node) continue;
                if (!children.includes(branches[i].nodes[j])) {
                    children.push(branches[i].nodes[j]);
                }
            }
        }
        // remove arguments from skolem terms:
        var nodestr = node.toString().replace(/(φ\d+)(\(.+?\))(?!\)|,)/g, function(m,p1,p2) {
            var res = p1;
            var extraClosed = (m.match(/\)/g) || []).length - (m.match(/\(/g) || []).length;
            for (var i=0; i<extraClosed; i++) res += ')';
            return res;
        });
        // nodestr = node.toString();
        var res = node.used + ' ' + nodestr + (node.__markClosed ? "<br>x<br>" : "<br>");
        if (children[1]) {
            var tdStyle = "font-family:monospace; border-top:1px solid #999; padding:3px; border-right:1px solid #999";
            var td = "<td align='center' valign='top' style='" + tdStyle + "'>"; 
            res += "<table><tr>"+ td + getTree(children[0], recursionDepth) +"</td>\n"
                + td + getTree(children[1], recursionDepth) + "</td>\n</tr></table>";
        }
        else if (children[0]) res += getTree(children[0], recursionDepth);
        return res;
    }
}

function Branch(tree, nodes, literals, freeVariables, todoList, closed) {
    this.tree = tree;
    this.nodes = nodes || [];
    this.literals = literals || [];
    this.freeVariables = freeVariables || [];
    this.todoList = todoList || [];
    this.closed = closed || false;
    this.id = 'b'+(Branch.counter++)+'.';
    this.string = ''; // a string representation, used in pruneAlternatives
}
Branch.counter = 0;

Branch.prototype.newVariable = function(isWorldTerm) {
    /**
     * return new variable for gamma expansion
     */
    var sym = isWorldTerm ? 'ζ' : 'ξ';
    var res = sym+'1';
    for (var i=this.freeVariables.length-1; i>=0; i--) {
        if (this.freeVariables[i][0] == sym) {
            res = sym+(this.freeVariables[i].substr(1)*1+1);
            break;
        }
    }
    this.freeVariables.push(res);
    return res;
}

Branch.prototype.tryClose = function(node, dontPrune) {
    /**
     * check if branch can be closed with the help of the newly added node
     * <node>, without applying unification
     */
    log('checking if branch can be closed with '+node);
    var complFormula = (node.formula.operator == '¬') ? node.formula.sub : node.formula.negate();
    var complNode;
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].formula.equals(complFormula)) {
            // prefer already used nodes as complementary nodes:
            if (this.nodes[i].used || !complNode) {
                complNode = this.nodes[i];
                if (complNode.used) break;
            }
        }
    }
    if (complNode) {
        log("+++ branch closed +++");
        this.tree.closeBranch(this, node, complNode);
        if (!dontPrune) {
            this.tree.prover.pruneAlternatives(this.tree);
        }
        return true;
    }
    return false;
}
    
Branch.prototype.unifierAffectsOtherBranches = function(unifier) {
    /**
     * check if any of the variables in the domain of <unifier> (a substitution)
     * occurs on another branch of the tree
     */
    for (var j=0; j<this.tree.openBranches.length; j++) {
        var branch = this.tree.openBranches[j];
        if (branch == this) continue;
        for (var i=0; i<unifier.length; i+=2) {
            if (branch.freeVariables.includes(unifier[i])) return true;
        }
    }
    return false;
}

Branch.prototype.closeWithEquality = function(solution) {
    /**
     * close branch with solved EqualityProblem <solution>
     */

    // As mentioned in Prover.equalityReasoner(), from where this function is
    // called, the current tree may be a copy of the tree for which <solution>
    // was made. In this case, terms1Node and terms2Node in <solution> point at
    // nodes that aren't on the present tree, and so do newNodes[i].fromNode
    // references to these nodes. We can find the right nodes on the present
    // tree by their node.id.
    
    for (var i=0; i<solution.newNodes.length; i++) {
        // Different solutions may involve overlapping newNodes. We want to
        // apply them to different trees (for backtracking) with non-overlapping
        // nodes (see e.g. pel49). So we copy the node.
        var node = solution.newNodes[i].copy();
        var nf0 = node.fromNodes[0];
        var nf1 = node.fromNodes[1];
        node.fromNodes[0] = this.getNodeById(node.fromNodes[0].id);
        node.fromNodes[1] = this.getNodeById(node.fromNodes[1].id);
        log("adding node " +node);
        this.addNode(node, true);
        node.expansionStep = this.tree.prover.step - solution.newNodes.length + i + 1;
    }
    var subs = solution.getSubstitution();
    log("applying substitution "+subs);
    this.tree.applySubstitution(subs);
    log(this.tree);
    var closingNode1 = this.getNodeById(solution.terms1Node.id);
    var closingNode2 = this.getNodeById(solution.terms2Node.id);
    this.tree.closeBranch(this, closingNode1, closingNode2);
    return;
}

Branch.prototype.getNodeById = function(id) {
    for (var i=this.literals.length-1; i>=0; i--) {
        if (this.literals[i].id == id) return this.literals[i];
    }
}

Branch.prototype.copy = function() {
    /**
     * return a copy of this branch with the same (===) nodes, for beta
     * expansions
     */
    var res = new Branch(this.tree,
                         this.nodes.copy(),
                         this.literals.copy(),
                         this.freeVariables.copy(),
                         this.todoList.copy(),
                         this.closed);
    res.string = this.string;
    return res;
}

Branch.prototype.addNode = function(node, dontSkip) {
    /**
     * add <node> to branch and inserts it expansion into the branch's todo
     * stack; if a node with the same formula is already on the branch, the
     * node is only added if <dontSkip> is true
     */
    var addToTodo = true;
    if (this.containsFormula(node.formula)) {
        if (dontSkip) addToTodo = false;
        else return null;
    }
    this.nodes.push(node);
    this.string += (this.string ? ',' : '')+node.formula.string;
    this.tree.string = this.tree.openBranches.map(function(b) { return b.string }).join('|');
    this.tree.numNodes++;
    if (node.type == 'literal') {
        this.literals.push(node);
    }
    if (!this.closed && addToTodo) {
        this.expandTodoList(node);
    }
    // so that we can later find nodes added in the same step:
    node.expansionStep = this.tree.prover.step;
    log(this.tree);
    return node;
}

Branch.prototype.containsFormula = function(formula) {
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].formula.string == formula.string) return true;
    }
    return false;
}

Branch.prototype.expandTodoList = function(node) {
    /**
     * insert node expansion into branch's todoList
     */
    var todo = node.getExpansionTask();
    // process newly added literals in one go:
    if (todo.nextRule == Prover.literal &&
        this.todoList[0] && this.todoList[0].nextRule == Prover.literal) {
        this.todoList[0].args.push(node);
    }
    else {
        for (var i=0; i<this.todoList.length; i++) {
            if (todo.priority <= this.todoList[i].priority) break;
            // '<=' is important so that new gamma nodes are processed before old ones
        }
        this.todoList.insert(todo, i);
    }
    
    if (this.tree.parser.isModal) {
        if (this.nodes.length == 1) {
            // add accessibility rules for initial world:
            this.addAccessibilityRuleApplications();
        }
        else if (node.formula.predicate == this.tree.parser.R) {
            this.addAccessibilityRuleApplications(node);
        }
    }
}

Branch.prototype.addAccessibilityRuleApplications = function(node) {
    /**
     * add special modal rules to todoList based on the added <node> 
     * 
     * Whenever a new world is first mentioned on a branch, rules like
     * seriality, transitivity etc. can potentially be applied with that
     * world. So we add these rules to todoList. Some rules like symmetry can
     * also be applied when wRv is first added for old worlds.
     */
    for (var i=0; i<this.tree.prover.accessibilityRules.length; i++) {
        var rule = this.tree.prover.accessibilityRules[i];
        var pos = this.todoList.length;
        while (pos > 0 && this.todoList[pos-1].priority >= rule.priority) pos--;
        if (node) {
            // Many accessibility rules don't meaningfully extend nodes of type
            // wRw.
            if (node.formula.terms[0] != node.formula.terms[1]
                || rule.premiseCanBeReflexive) {
                this.todoList.insert(Prover.makeTodoItem(rule, [node]), pos);
            }
        }
        else {
            // Many accessibility rules don't meaningfully apply without any
            // premises of form wRv.
            if (!rule.needsPremise) {
                this.todoList.insert(Prover.makeTodoItem(rule, []), pos);
            }
        }
    }
}

Branch.prototype.getClosingUnifiers = function(node) {
    /**
     * check if branch can be closed by applying a substitution, involving the
     * newly added literal <node> as either the member of a complementary pair
     * or as a self-complementary node ¬(Φ=Φ); return list of substitutions
     * that allow closing the branch 
     */

    log("checking if "+node+" can be made complementary with other node on the branch");
    var nodeAtom = node.formula.sub || node.formula;
    var unifiersHash = {}; // for duplicate detection
    for (var i=this.literals.length-1; i>=0; i--) {
        var otherNode = this.literals[i];
        if (otherNode == node) continue;
        if (!otherNode.formula.sub == !node.formula.sub) continue;
        var otherAtom = otherNode.formula.sub || otherNode.formula;
        if (otherAtom.predicate != nodeAtom.predicate) continue;
        var u = Formula.unifyTerms(nodeAtom.terms, otherAtom.terms);
        log("unification with "+otherNode+" "+(u===false ? "impossible" : "possible: "+u));
        if (u.isArray) {
            unifiersHash[u.toString()] = u;
        }
    }
    
    if (nodeAtom.predicate == '=' && node.formula.sub) {
        log("checking if "+node+" can be turned into ¬(Φ=Φ)");
        var u = Formula.unifyTerms([nodeAtom.terms[0]], [nodeAtom.terms[1]]);
        if (u.isArray) {
            log("yes: "+u);
            unifiersHash[u.toString()] = u;
        }
    }
    return Object.values(unifiersHash);
}

Branch.prototype.createEqualityProblems = function(nodes) {
    /**
     * create equality problems that arise from <nodes>
     *
     * We test whether each node in <nodes> is a negated equality node ¬(s=t) or
     * a node of form +-Ps1..sn that has a potentially complementary node
     * -+Pt1..tn; if yes, we create an EqualityProblem with the target of
     * unifying s and t or s1=t1..sn=tn. If instead a node in <nodes> is an
     * equality node s=t, we need to re-schedule earlier equality problems with
     * the new equation(s).
     */

    nodes = nodes.filter(function(n) {
        // skip t=t nodes
        return !(n.formula.predicate == '='
                 && n.formula.terms[0].toString() == n.formula.terms[1].toString());
    });
    for (var i=0; i<nodes.length; i++) {
        if (nodes[i].formula.predicate == '=') {
            // new equation; call equality reasoner for all problems on branch:
            var recNodes = this.literals.filter(function(lit) {
                // select only negated literals, so that we also re-evaluated
                // potentially self-complentary nodes, but don't re-re-evaluate
                // nodes based on earlier equality nodes
                return lit.formula.sub;
            });
            return this.createEqualityProblems(recNodes);
        }
    }
    var res = [];
    for (var i=0; i<nodes.length; i++) {
        var node = nodes[i];
        if (node.formula.sub && node.formula.sub.predicate == '=') {
            // ¬(s=t)
            var prob = this.createEqualityProblem(node, node)
            if (prob) res.push(prob);
        }
        else {
            // Ps=..sn or ¬Ps1..sn
            for (var j=0; j<this.literals.length; j++) {
                var lit = this.literals[j];
                if ((node.formula.sub && lit.formula.predicate == node.formula.sub.predicate) ||
                    (lit.formula.sub && node.formula.predicate == lit.formula.sub.predicate)) {
                    var prob = this.createEqualityProblem(node, lit);
                    if (prob) res.push(prob);
                }
            }
        }
    }
    return res;
}

Branch.prototype.createEqualityProblem = function(node1, node2) {
    /**
     * create EqualityProblem whose target is to unify <node1> and <node2>
     * based on the eqations on the current branch
     */
    var equations = this.literals.filter(function(n) {
        return n.formula.predicate == '='
            && ![n.formula.terms[0]].equals([n.formula.terms[1]]);
    });
    if (!equations.length) return null;
    equations.reverse(); // prefer applying LL to late equations
    log('creating equality problem based on '+(node1==node2 ? node1 : node1+' and '+node2));
    var prob = new EqualityProblem();
    prob.init(equations, node1, node2);
    return prob;
}

Branch.prototype.toString = function() {
    return this.string;
}

function Node(formula, fromRule, fromNodes) {
    if (!formula) return;
    this.formula = formula;
    this.type = formula.type;
    this.id = Node.counter++;
    // Each non-initial node on a branch is the result of applying a rule to
    // (zero or more) earlier nodes on the same branch. This information about a
    // node's origin is needed to display the final sentence tableau, and for
    // pruning branches (see pruneBranch).
    this.fromRule = fromRule || null;
    this.fromNodes = fromNodes || [];
    this.used = ''; // (string) list of branch ids for whose closure this node is used
}
Node.counter = 0;

Node.prototype.getExpansionTask = function() {
    /**
     * return todo item for expanding this node
     */
    var todo = {
        nextRule: Prover[this.type],
        priority: Prover[this.type].priority,
        args: [this]
    }
    // heuristic: expand ∀..∃.. nodes before entirely universal nodes:
    if (this.type == 'gamma' && this.formula.string.includes('∃')) {
        todo.priority -= 0.5;
    }
    else if (this.type == 'modalGamma' && this.formula.string.includes('◇')) {
        todo.priority -= 0.5;
    }
    return todo;
}

Node.prototype.copy = function() {
    var res = new Node();
    res.formula = this.formula;
    res.fromRule = this.fromRule;
    res.fromNodes = this.fromNodes.copy();
    res.type = this.type;
    res.id = this.id;
    res.used = this.used;
    return res;
}

Node.prototype.toString = function() {
    return this.formula.toString();
}
