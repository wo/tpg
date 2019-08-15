//
// When building free-variable tableaux, one sometimes faces the
// choice of either closing a branch by unifying terms or expanding
// another formula. There is no effective rule for which choice is
// best under given conditions. So a common strategy, also used here,
// is to choose the first option, but store the other in memory so
// that one can return to it in case the original choice doesn't lead
// to a closed tree. Of course it's impossible to decide whether a
// choice will eventually lead to a closed tree, so backtracking is
// initiated when the tableau has reached a certain degree of
// complexity (determined by the number of free variables and nodes on
// the current branch).

function Prover(initFormulas, parser, accessibilityConstraints) {

    log("initializing prover");

    // init formulas; i.e. normalize, translate modal sentences, set up
    // accessibility rules:
    this.initFormulas = initFormulas; // formulas as entered, with conclusion negated
    this.parser = parser.copy();
    this.accessibilityRules = [];
    if (parser.isModal) {
        this.initFormulasNonModal = [];
        for (var i=0; i<initFormulas.length; i++) {
            this.initFormulasNonModal.push(this.parser.translateFromModal(initFormulas[i]));
        }
        if (accessibilityConstraints) {
            this.s5 = accessibilityConstraints.includes('universality');
            if (!this.s5) {
                this.accessibilityRules = accessibilityConstraints.map(function(s) {
                    return Prover[s];
                });
            }
        }
    }
    else {
        this.initFormulasNonModal = initFormulas;
    }
    this.initFormulasNormalized = this.initFormulasNonModal.map(function(f){
        return f.normalize();
    });
    
    // init prover:
    this.pauseLength = 2; // ms pause between calculations
    this.maxStepDuration = 20; // ms before setTimeout pause
    this.step = 0; // counter of calculation steps
    this.depthLimit = 2; // how many free variables may occur on the tree before
                         // backtracking; in addition, depthLimit * 4 is the
                         // upper bound for number of nodes on a branch before
                         // backtracking; value empirically chosen
    this.tree = new Tree(this);
    this.alternatives = []; // alternative trees stored for backtracking

    // init modelfinder:
    var mfParser = this.parser.copy();
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
            return mfParser.parseAccessibilityFormula(name2fla[s]).normalize();
        });
        // todo: strip redundant constraints
        this.modelfinder = new ModelFinder(
            this.initFormulasNormalized,
            mfParser,
            accessibilityFormluas,
            this.s5
        );
    }
    else {
        this.modelfinder = new ModelFinder(this.initFormulasNormalized, mfParser);
    }
    this.counterModel = null;

    this.stepStartTime = performance.now();
    
    this.start = function() {
        this.nextStep();
    };

    this.stop = function() {
        this.stopTimeout = true;
    };

    this.onfinished = function() {};
    
    this.status = function() {};

}

Prover.prototype.nextStep = function() {

    // if (this.tree.closedBranches.length >= 6) {
    //     var branch = this.tree.closedBranches[5]
    //     var lastNode = branch.nodes[branch.nodes.length-1];
    //     var prevNode = branch.nodes[branch.nodes.length-2];
    //     if (lastNode.fromRule == Prover.alpha &&
    //         lastNode.fromNodes != prevNode.fromNodes) {
    //         log(lastNode.formula.string);
    //         log(prevNode.formula.string);
    //         log(lastNode.fromNodes[0].formula.string);
    //         log(prevNode.fromNodes[0].formula.string);
    //     }
    // }

    
    // expands the next node on the present tree; then initializes backtracking
    // if limit is reached and occasionally searches for a countermodel; calls
    // itself again unless proof is complete.
    this.step++;
    log('*** prover step '+this.step);
    
    // status msg: xxx tidy up
    var numBranches = this.tree.openBranches.length + this.tree.closedBranches.length;

    // expand leftmost open branch on tree:
    // (todoList items look like this: [Prover.alpha, nodes[0]])
    log(this.tree.openBranches[0].todoList);
    var todo = this.tree.openBranches[0].todoList.shift();
    if (!todo) { // xxx can this ever happen?
        log('tree open and complete');
        return this.onfinished(0);
    }
    var nextRule = todo.shift();
    var args = todo;
    nextRule(this.tree.openBranches[0], args);
    log(this.tree);
    
    // xxx should we check if a rule (say gamma) could be applied but didn't add
    // any new nodes (e.g. because of duplicate node detection), in which case
    // the tree remains open?
    
    if (this.tree.openBranches.length == 0) {
        log('tree closed');
        return this.onfinished(1);
    }
    
    if (this.tree.openBranches[0].nodes.length > this.depthLimit * 4) {
        log('reached complexity limit for backtracking');
        this.limitReached();
    }
    
    // search for a countermodel:
    if (this.modelfinder.nextStep()) {
        this.counterModel = this.modelfinder.model;
        return this.onfinished(0);
    }
    
    if (this.step % 20 == 19) {
        // Often, there are thousands of trees to check with depth n, and none
        // of them closes, whereas many close for n+1. Changing the depth
        // measure doesn't change this. Instead, once every x steps, we increase
        // the limit for a while and then reset it:
        if (this.step % 1000 == 999) {
            log("trying with increased depth for a few steps");
            this.depthLimit++;
            this.decreaseLimit = this.step + 200;
        }
        else if (this.step == this.decreaseLimit) {
            log("resetting depth");
            this.depthLimit--;
        }
    }

    if (this.stopTimeout) {
        // proof manually interrupted
        this.stopTimeout = false;
    }
    else if (this.pauseLength &&
             performance.now() - this.stepStartTime > this.maxStepDuration) {
        // continue with next step after short break to display status message
        // and not get killed by browsers
        setTimeout(function(){
            this.stepStartTime = performance.now();
            this.nextStep();
        }.bind(this), this.pauseLength*this.tree.numNodes/2);
    }
    else {
        this.nextStep();
    }
}

Prover.prototype.limitReached = function() {
    if (this.alternatives.length) {
        log(" * limit reached, trying stored alternative * ");
        log(this.alternatives.length+' alternatives');
        this.tree = this.alternatives.pop();
        log(this.tree);
    }
    else {
        this.depthLimit++;
        log("----- increasing depthLimit to " + this.depthLimit + " -----");
        this.tree = new Tree(this);
    }
}

Prover.prototype.tryAlternative = function() {
    // called if a branch can't be closed
    if (this.alternatives.length) {
        log(" * proof failed, trying stored alternative * ");
        log(this.alternatives.length+' alternatives');
        this.tree = this.alternatives.pop();
        log(this.tree);
        return true;
    }
    return false;
}

// If a rule leads to several new nodes, the third arguments to new Node()
// should be strictly identical, so that we can easily find these new nodes
// later

Prover.alpha = function(branch, nodeList) {
    log('alpha '+nodeList[0]);
    var node = nodeList[0];
    var subnode1 = new Node(node.formula.sub1, Prover.alpha, nodeList);
    var subnode2 = new Node(node.formula.sub2, Prover.alpha, nodeList);
    branch.addNode(subnode1);
    branch.addNode(subnode2);
    // tryClose is not part of addNode because we want to make sure both nodes
    // are added in the finished tree (this matters in the alternatives clause
    // of unification).
    branch.tryClose(subnode1);
    if (!branch.closed) branch.tryClose(subnode2);
}
Prover.alpha.priority = 1;
Prover.alpha.toString = function() { return 'alpha' }

Prover.beta = function(branch, nodeList) {
    log('beta '+nodeList[0]);
    var node = nodeList[0];
    branch.tree.openBranches.unshift(branch.copy());
    var subnode1 = new Node(node.formula.sub1, Prover.beta, nodeList);
    var subnode2 = new Node(node.formula.sub2, Prover.beta, nodeList);
    branch.tree.openBranches[0].addNode(subnode2);
    branch.addNode(subnode1);
    branch.tryClose(subnode1);
    branch.tree.openBranches[0].tryClose(subnode2);
}
Prover.beta.priority = 10;
Prover.beta.toString = function() { return 'beta' }

Prover.gamma = function(branch, nodeList, matrix) {
    // <matrix> is set when this is called from modalGamma for S5 trees, see
    // modalGamma() below.
    log('gamma '+nodeList[0]);
    var node = nodeList[0];
    if (branch.freeVariables.length == this.depthLimit) {
        log("depthLimit " + this.depthLimit + " exceeded!");
        this.limitReached();
        return null;
    }
    
    // The following lines would incorporate the Herbrand restriction on sentence tableau: 
    // do not expand a gamma node more often than there are constants on the branch.
    // For this purpose, s(0) and s(s(0)) should count as different constants, but 
    // branch.constants only contains [s,0], so I would have to keep track of the actual
    // instances somewhere. So for now, that's disabled. (2005-02-02) xxx todo
    // if (!node.numExpansions) node.numExpansions = [];
    // if (!node.numExpansions[branch.id]) node.numExpansions[branch.id] = 1;
    // else {
    //  node.numExpansions[branch.id]++;
    //  if (node.numExpansions[branch.id] > branch.constants.length + 1) {
    //      log("Branch unclosable by Herbrand restriction: " + node.numExpansions[branch.id] + " expansions, " + branch.constants.length + " constants on branch");
    //      // too many gamma instances. But not all is lost if we can backtrack:
    //      return this.backtrack() ? 0 : -1;
    //  }
    //}

    var isModalGamma = matrix ? true : false;
    var matrix = matrix || node.formula.matrix;
    var vacuous = matrix.string.indexOf(node.formula.variable) == -1; // xxx doesn't catch vacuous qu. in ∀x∃xFx
    if (vacuous) {
        // don't introduce new free variable if quantifier is vacuous:
        var newFormula = matrix;
    }
    else {
        var newVariable = branch.newVariable(matrix);
        var newFormula = matrix.substitute(node.formula.variable, newVariable);
        // add application back onto todoList:
        if (!isModalGamma) branch.todoList.push([Prover.gamma, node]);
    }
    var newNode = new Node(newFormula, Prover.gamma, nodeList); // xxx note that this sets fromRule to gamma even for s5 modal gamma nodes. is that ok?
    newNode.instanceTerm = newVariable; // used in sentree
    branch.addNode(newNode);
    branch.tryClose(newNode);
}
Prover.gamma.priority = 8;
Prover.gamma.toString = function() { return 'gamma' }

Prover.modalGamma = function(branch, nodeList) {
    // □A and ¬◇A nodes are translated into ∀x(¬wRxvAx) and ∀x(¬wRx∨¬Ax). By the
    // standard gamma rule, these would be expanded to ¬wRξ7 ∨ Aξ7 or ¬wRξ7 ∨
    // ¬Aξ7. We don't want these nodes to appear on the displayed tree.
    // More importantly, when these nodes are expanded, we get a ¬wRξ7 branch
    // which also shouldn't appear on the displayed tree. That's easy to handle
    // if the branch immediately closes (through unification, presumably).
    // But there's no guarantee for that, since (1) we actively explore
    // alternative trees in which unification is not applied, and (2) expansions
    // of ∀x(¬wRx ∨ Ax) are allowed even if there's no node of the form wRy on
    // the tree, so that unification is impossible.
    //
    // More importantly, if we require the ¬wRξ7 branch to close immediately, we
    // effectly don't make use of free world variables in the tableau
    // construction: a □A node is expanded to ¬wRξ7 ∨ Aξ7, alright, but further
    // expansion is only allowed if some wRv occurs on the branch, in which case
    // the expansion (effectively) adds Av to the branch. We can reach the same
    // effect with the textbook □A rule: allow expansion only if some wRv occurs
    // on the branch; in that case add Av to the branch.

    log('modalGamma '+nodeList[0]);
    var node = nodeList[0];
    // add application back onto todoList:
    branch.todoList.push([Prover.modalGamma, node]);
    
    if (branch.tree.prover.s5) {
        // In S5, we still translate □A into ∀x(¬wRxvAx) rather than the simpler
        // ∀xAx. That's because the latter doesn't tell us at which world the
        // formula is evaluated ('w'), which makes it hard to translate back
        // into textbook tableaux. (Think about the tableau for ◇□A→□A.) But
        // when we expand the □A node, we ignore the accessibility
        // clause. Instead, we expand ∀x(¬wRx∨Ax) to Aξ1 and use the
        // free-variable machinery.
        return Prover.gamma(branch, nodeList, node.formula.matrix.sub2);
    }

    var wRx = node.formula.matrix.sub1.sub;
    var w = wRx.terms[0];
    var wR = wRx.predicate + w;
    log('wRx: '+wRx+', w: '+w);
    // find wR* node for □A expansion:
    OUTERLOOP:
    for (var i=0; i<branch.literals.length; i++) {
        log('lit '+branch.literals[i]);
        if (branch.literals[i].formula.string.indexOf(wR) == 0) {
            var wRy = branch.literals[i];
            // check if <node> has already been expanded with this wR* node:
            for (var j=0; j<branch.nodes.length; j++) {
                if (branch.nodes[j].fromRule == Prover.modalGamma &&
                    branch.nodes[j].fromNodes[0] == node &&
                    branch.nodes[j].fromNodes[1] == wRy) {
                    log('already used');
                    continue OUTERLOOP;
                }
            }
            log('expanding!');
            // expand <node> with found wR*:
            var modalMatrix = node.formula.matrix.sub2;
            var v = wRy.formula.terms[1];
            log(modalMatrix);
            var newFormula = modalMatrix.substitute(node.formula.variable, v);
            log(newFormula);
            var newNode = new Node(newFormula, Prover.modalGamma, [node, wRy]);
            newNode.instanceTerm = v;
            branch.addNode(newNode);
            branch.tryClose(newNode);
            break;
        }
    }
}
Prover.modalGamma.priority = 9;
Prover.modalGamma.toString = function() { return 'modalGamma' }
    
Prover.delta = function(branch, nodeList, matrix) {
    // <matrix> is set when this is called from modalDelta for S5 trees, see
    // modalDelta() below. 
    log('delta '+nodeList[0]);
    var node = nodeList[0];
    var fla = node.formula;
    // find skolem term (newTerm):
    var funcSymbol = branch.newFunctionSymbol(matrix);
    // It suffices to skolemize on variables contained in this formula.
    // This makes some proofs much faster by making some gamma applications
    // redundant. However, translation into sentence tableau then becomes
    // almost impossible, because here we need the missing gamma
    // applications.  Consider Ax(Fx & Ey~Fy).
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
    log('modalDelta '+nodeList[0]);
    var node = nodeList[0];
    if (branch.tree.prover.s5) {
        // In S5, we still translate ◇A into ∃x(wRx∧Ax) rather than the simpler
        // ∃xAx. That's because the latter doesn't tell us at which world the
        // formula is evaluated ('w'), which makes it hard to translate back
        // into textbook tableaux. (Think about the tableau for ◇□A→□A.) But
        // when we expand the ◇A node, we ignore the accessibility
        // clause. Instead, we expand ∃x(wRx∧Ax) to Aφ, where φ is a suitable
        // skolem term, just like for ordinary existential formulas.
        return Prover.delta(branch, nodeList, node.formula.matrix.sub2);
    }
    var fla = node.formula;
    // don't need skolem terms for diamond formulas ∃v(wRv ∧ Av):
    var newWorldName = branch.newWorldName();
    var newFormula = node.formula.matrix.substitute(node.formula.variable, newWorldName);
    // xxx might as well expand the conjunction, then I don't need to remove it in sentree!
    var newNode = new Node(newFormula, Prover.delta, nodeList);
    newNode.instanceTerm = newWorldName;
    branch.addNode(newNode);
    branch.tryClose(newNode);
}
Prover.modalDelta.priority = 2;
Prover.modalDelta.toString = function() { return 'modalDelta' }

Prover.reflexivity = function(branch, nodeList) {
    log('applying reflexivity rule');
    // nodeList is either empty or contains a node of form wRv
    // wherein v might have been newly introduced
    if (nodeList.length==0) {
        // applied to initial world w:
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
    branch.tryClose(newNode);
}
Prover.reflexivity.priority = 3;
Prover.reflexivity.toString = function() { return 'reflexivity' }

Prover.symmetry = function(branch, nodeList) {
    log('applying symmetry rule');
    // nodeList is either empty or contains a node of form wRv.
    if (nodeList.length == 0) {
        // applied to initial world w; nothing to do.
        return;
    }
    var nodeFormula = nodeList[0].formula;
    var R = branch.tree.parser.R;
    var formula = new AtomicFormula(R, [nodeFormula.terms[1], nodeFormula.terms[0]]);
    log('adding '+formula);
    var newNode = new Node(formula, Prover.symmetry, nodeList);
    if (branch.addNode(newNode)) {
        branch.tryClose(newNode);
    }
}
Prover.symmetry.priority = 3;
Prover.symmetry.toString = function() { return 'symmetry' }

Prover.transitivity = function(branch, nodeList) {
    log('applying transitivity rule');
    // nodeList is either empty or contains a newly added node of form wRv.
    if (nodeList.length == 0) {
        // applied to initial world w; nothing to do.
        return;
    }
    var R = branch.tree.parser.R;
    var node = nodeList[0];
    var nodeFla = node.formula;
    // see if we can apply transitivity:
    for (var i=0; i<branch.nodes.length-1; i++) {
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
            log('adding '+newFla);
            var newNode = new Node(newFla, Prover.transitivity, [branch.nodes[i], node]);
            if (branch.addNode(newNode)) {
                branch.tryClose(newNode);
            }
        }
    }
}
Prover.transitivity.priority = 3;
Prover.transitivity.toString = function() { return 'transitivity' }

Prover.euclidity = function(branch, nodeList) {
    log('applying euclidity rule');
    // nodeList is either empty or contains a newly added node of form wRv.
    if (nodeList.length == 0) {
        // applied to initial world w; nothing to do.
        return;
    }
    var R = branch.tree.parser.R;
    var node = nodeList[0];
    var nodeFla = node.formula;
    // see if we can apply euclidity:
    for (var i=0; i<branch.nodes.length-1; i++) {
        var earlierFla = branch.nodes[i].formula;
        if (earlierFla.predicate != R) continue;
        if (earlierFla.terms[0] == nodeFla.terms[0]) {
            // earlierFla wRu, nodeFla wRv
            var newFlas = [
                new AtomicFormula(R, [earlierFla.terms[1], nodeFla.terms[1]]),
                new AtomicFormula(R, [nodeFla.terms[1], earlierFla.terms[1]])
            ];
            // xxx adding two formulas isn't ideal because it means even unused
            // ones will remain on the displayed tree, e.g. in ◇□p →□◇p; better
            // add second application with same nodeList back on todo stack.
            for (var j=0; j<newFlas.length; j++) {
                log('adding '+newFlas[j]);
                var newNode = new Node(newFlas[j], Prover.euclidity, [branch.nodes[i], node]);
                if (branch.addNode(newNode)) {
                    branch.tryClose(newNode);
                }
            }
        }
    }
}
Prover.euclidity.priority = 3;
Prover.euclidity.toString = function() { return 'euclidity' }

Prover.seriality = function(branch, nodeList) {
    log('applying seriality rule');
    // nodeList is either empty or contains a newly added node of form wRv.
    var R = branch.tree.parser.R;
    if (nodeList.length == 0) {
        // applied to initial world w.
        var oldWorld = branch.tree.parser.w;
    }
    else {
        var oldWorld = nodeList[0].formula.terms[1];
        // check if oldWorld can already see a world:
        for (var i=0; i<branch.nodes.length-1; i++) {
            var earlierFla = branch.nodes[i].formula;
            if (earlierFla.predicate == R && earlierFla.terms[0] == oldWorld) {
                log(oldWorld+' can already see a world');
                return;
            }
        }
    }
    var newWorld = branch.newWorldName();
    var newFla = new AtomicFormula(R, [oldWorld, newWorld]);
    log('adding '+newFla);
    var newNode = new Node(newFla, Prover.seriality, []);
    if (branch.addNode(newNode)) {
        branch.tryClose(newNode);
    }
}
Prover.seriality.priority = 10;
Prover.seriality.toString = function() { return 'seriality' }

function Tree(prover) {
    if (!prover) return; // for copy() function
    this.prover = prover;
    this.parser = prover.parser;
    var initBranch = new Branch(this);
    for (var i=0; i<prover.initFormulasNormalized.length; i++) {
        var formula = prover.initFormulasNormalized[i];
        var node = new Node(formula);
        initBranch.addNode(node);
    }
    this.openBranches = [initBranch];
    this.closedBranches = [];
    this.numNodes = 0;
}

Tree.prototype.closeBranch = function(branch, complementary1, complementary2) {
    branch.closed = true;
    this.markUsedNodes(branch, complementary1, complementary2);
    log(this);
    this.pruneBranch(branch, complementary1, complementary2);
    this.openBranches.remove(branch);
    this.closedBranches.push(branch);
    this.pruneAlternatives();
}

Tree.prototype.pruneAlternatives = function() {
    // discard all alternatives whose open branches are a superset of
    // this.openBranches; otherwise a lot of time is spent in complex proofs
    // exploring alternatives that reopen already closed branches without making
    // progress on open ones.  xxx doesn't work: see step 138 in ∀x∃y(Fx ↔ Gy) ↔
    // ∃y∀x(Fx → Gy)∧∃y∀x(Gy → Fx): here all branches emerging from one disjunct
    // are closed, but we still reopen the disjunct. The problem
    var alternatives = this.prover.alternatives.copy();
    ALTLOOP:
    for (var i=0; i<alternatives.length; i++) {
        var altTree = alternatives[i];
        for (var j=0; j<this.openBranches.length; j++) {
            var openBranch = this.openBranches[j];
            if (!altTree.containsOpenBranch(openBranch)) { // xxx optimise: containsopenbranch looks through all open branches for each call
                // log('alternative '+i+' does not contain open branch '+openBranch);
                continue ALTLOOP
            }
        }
        log('alternative '+i+' contains all open branch of this tree; removing');
        this.prover.alternatives.remove(altTree);
    }
}

Tree.prototype.containsOpenBranch = function(branch) {
    // check if tree contains an open branch with the same kind of nodes as
    // <branch>; used in pruneAlternatives
    BRANCHLOOP:
    for (var i=0; i<this.openBranches.length; i++) {
        var oBranch = this.openBranches[i];
        if (branch.nodes.length != oBranch.nodes.length) continue;
        for (var j=1; j<branch.nodes.length; j++) {
            if (branch.nodes[j].formula.string != oBranch.nodes[j].formula.string) {
                continue BRANCHLOOP;
            }
        }
        return true;
    }
    return false;
}

Tree.prototype.markUsedNodes = function(branch, complementary1, complementary2) {
    // mark nodes with .used = true if they were involved in deriving the
    // complementary pair
    var ancestors = [complementary1, complementary2];
    var n;
    while ((n = ancestors.shift())) {
        if (!n.used) {
            for (var i=0; i<n.fromNodes.length; i++) {
                ancestors.push(n.fromNodes[i]);
            }
            n.used = true;
        }
    }
}


Tree.prototype.pruneBranch = function(branch, complementary1, complementary2) {
    // When a branch is closed, we look for branching steps that weren't used to
    // derive the complementary pair; we undo these steps and remove the other
    // branches originating from them.
    //
    // Example:
    //
    //           /-B--    can be removed (no matter if it's open or closed)
    // --Z--(AvB)       
    //           \-A-¬Z   x (AvB unused)
    //
    // A more tricky case:
    //
    //                        /-D--   
    //           /-B-----(CvD)
    // --Z--(AvB)             \-C-¬Z   x (AvB unused, CvD used)
    //           \-A---
    //
    // If the branch with D is closed, the A branch can be removed (no matter if
    // it's open or closed). But if the D branch is open, the so-far unused node
    // B may be needed to close that branch. So we have to keep the AvB
    // expansion. (It will be removed if the B node is not used when closing the
    // D branch.)
    //
    // The general strategy is to walk up from the endpoint of the closed branch
    // until we reach a used branching node from which another open branch
    // emerges; any unused branching up to that point is removed.
    //
    // NB: in tests this is almost never used :(
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
                    if (obranches[j].closed) this.closedBranches.remove(obranches[j]);
                    else this.openBranches.remove(obranches[j]);
                    // We don't remove the beta expansion result on this branch;
                    // it'll be removed in the displayed sentence tree because
                    // it has .used == false
                }
            }
        }
    }
    return;

    // original code:
    toRoot:
    for (var i=branch.nodes.length-1; branch.nodes[i].developedFrom; i--) {
        if (branch.nodes[i].developedFrom.type != 'beta') continue;
        // if on a branch with nodes [n1,...,n17] BETA is applied, the result
        // are two branches [n1,...,n17,b1], [n1,...,n17,b2]. b1 and b2 have the
        // same index.
        for (var j=0; j<this.openBranches.length; j++) {
            var obranch = this.openBranches[j];
            if (obranch == branch) continue;
            if (obranch.nodes[i] &&
                obranch.nodes[i].developedFrom == branch.nodes[i].developedFrom &&
                obranch.nodes[i] != branch.nodes[i]) {
                // another open branch originating here
                if (branch.nodes[i].used) {
                    // can't look any further because from here upwards this
                    // subtree isn't closed
                    break toRoot;
                }
                log("pruning branch "+obranch+" originating from unused node "+branch.nodes[i].developedFrom);
                this.openBranches.remove(obranch);
                // note that we don't remove the beta expansion result on the
                // closed branch.
                break;
            }
        }
    }
}

Tree.prototype.closeCloseableBranches = function() {
    // close branches without unification
    // xxx does this handle double negations correctly?
    var openBranches = this.openBranches.copy();
    for (var k=0; k<openBranches.length; k++) {
        var branch = openBranches[k];
        // log('?b: '+branch);
        BRANCHLOOP:
        for (var i=branch.nodes.length-1; i>=0; i--) {
            var n1 = branch.nodes[i];
            var n1negated = (n1.formula.operator == '¬');
            var closed = false;
            for (var j=i-1; j>=0; j--) {
                var n2 = branch.nodes[j];
                // log('? '+n1+' '+n2);
                if (n2.formula.operator == '¬') {
                    if (n2.formula.sub.equals(n1.formula)) closed = true;
                }
                else if (n1negated) {
                    if (n1.formula.sub.equals(n2.formula)) closed = true;
                }
                if (closed) {
                    this.closeBranch(branch, n1, n2);
                    log("+++ branch closed +++");
                    break BRANCHLOOP;
                }
            }
        }
    }
}

Tree.prototype.copy = function() {
    // return a deep copy, including copy of nodes (but not of formulas)
    var ntree = new Tree();
    var nodemap = {} // old node id => copied Node
    ntree.prover = this.prover;
    ntree.parser = this.parser;
    ntree.numNodes = this.numNodes;
    ntree.openBranches = [];
    for (var i=0; i<this.openBranches.length; i++) {
        ntree.openBranches.push(copyBranch(this.openBranches[i]));
    }
    ntree.closedBranches = [];
    for (var i=0; i<this.closedBranches.length; i++) {
        ntree.closedBranches.push(copyBranch(this.closedBranches[i]));
    }
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
            var todo = [orig.todoList[i][0]];
            for (var j=1; j<orig.todoList[i].length; j++) {
                todo.push(nodemap[orig.todoList[i][j].id]);
            }
            todoList.push(todo);
        } 
        var b = new Branch(ntree, nodes, literals,
                           orig.freeVariables.copy(),
                           orig.skolemSymbols.copy(),
                           todoList, orig.closed);
        b.id = orig.id;
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

Tree.prototype.genericcopy = function() { // xxx remove
    // Returns a deep copy. This is a generic clone function due to Brendan Eich. 
    // It should be simplified because it slows down proofs.
    function cloneObjectGraph(obj) {
        var copy = new obj.constructor;
        obj._mark = copy;
        for (var i in obj) {
            if (i == '_mark') continue;
            var pval = obj[i];
            if (typeof pval == "object" && pval != null) {
                pval = pval._mark ? pval._mark : cloneObjectGraph(pval);
            }
            copy[i] = pval;
        } 
        return copy;
    }
    function removeMarksFromObjectGraph(obj) {
        delete obj._mark;
        for (var i in obj) {
            var pval = obj[i];
            if (typeof pval == "object" && pval != null && pval._mark) {
                removeMarksFromObjectGraph(pval);
            }
        }
    }
    var copy = cloneObjectGraph(this);
    removeMarksFromObjectGraph(this);
    return copy;
}

Tree.prototype.applySubstitution = function(sub) {
    // apply substitution of terms for variables to all nodes on tree
    var branches = this.openBranches.concat(this.closedBranches); // xxx optimise! e.g., why process closed branches at all?
    for (var i=0; i<sub.length; i+=2) {
        var nodeProcessed = {};
        for (var b=0; b<branches.length; b++) {
            for (var n=branches[b].nodes.length-1; n>=0; n--) {
                var node = branches[b].nodes[n]; 
                if (nodeProcessed[node.id]) break;
                nodeProcessed[node.id] = true;                    
                node.formula = node.formula.substitute(sub[i], sub[i+1]);
                if (node.instanceTerm) {
                    node.instanceTerm = AtomicFormula.substituteInTerm(node.instanceTerm, sub[i], sub[i+1]);
                }
            }
            branches[b].freeVariables.remove(sub[i]);
        }
    }
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
    return res;
    
    function getTree(node) { 
        var recursionDepth = arguments[1] || 0;
        if (++recursionDepth > 50) return "<b>...<br>[max recursion]</b>";
        var children = [];
        for (var i=0; i<branches.length; i++) {
            for (var j=0; j<branches[i].nodes.length; j++) {
                if (branches[i].nodes[j-1] != node) continue;
                if (!children.includes(branches[i].nodes[j])) {
                    children.push(branches[i].nodes[j]);
                }
            }
        }
        var res = (node.used ? '.' : '') + node + (node.__markClosed ? "<br>x<br>" : "<br>");
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

function Branch(tree, nodes, literals, freeVariables, skolemSymbols, todoList, closed) {
    this.tree = tree;
    this.nodes = nodes || [];
    this.literals = literals || [];
    this.freeVariables = freeVariables || [];
    this.skolemSymbols = skolemSymbols || [];
    this.todoList = todoList || [];
    // todoList looks like this: [[Prover.alpha, nodes[0]], [Prover.seriality]]
    this.closed = closed || false;
    this.id = Branch.counter++;
}
Branch.counter = 0;

Branch.prototype.newVariable = function(isWorldTerm) {
    // return new variable for gamma expansion
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

Branch.prototype.newFunctionSymbol = function(isWorldTerm) {
    // return new constant/function symbol for delta expansion
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

Branch.prototype.newWorldName = function() {
    return this.newFunctionSymbol(true);
}

Branch.prototype.tryClose = function(node) {
    // check if branch can be closed with the help of the newly added node
    // <node>.
    
    log('checking if branch can be closed with '+node);
    // First check if closure is possible without unification:
    var negatedFormula = (node.formula.operator == '¬') ? node.formula.sub : node.formula.negate();
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].formula.equals(negatedFormula)) {
            this.tree.closeBranch(this, node, this.nodes[i]);
            log("+++ branch closed +++");
            return true;
        }
    }
    
    // Now check for closure with unification. There may be several options,
    // with different substitutions. It may also be better to not unify at all
    // and instead continue expanding nodes. So we collect all possible
    // unifiers, try the first and copy alternative trees for later exploration
    // with backtracking.
    if (node.type != 'literal') return false; // Formula.unify() only works for
                                              // literals
    var unifiers = []; // list of substitutions
    var otherNodes = []; // corresponding list of other nodes
    for (var i=this.literals.length-1; i>=0; i--) {
        if (this.literals[i] == node) continue;
        var u = negatedFormula.unify(this.literals[i].formula);
        if (u.isArray) {
            // make sure unifier is new:
            var isNew = true;
            for (var j=0; j<unifiers.length; j++) {
                if (unifiers[j].equals(u)) isNew = false;
            }
            if (isNew) {
                unifiers.push(u);
                otherNodes.push(this.literals[i]); 
            }
        }
    }
    if (unifiers.length == 0) {
        return false;
    }
    // xxx todo: use simpler unifiers first! ¬(Pa∧¬Pf(f(a))∧∀x(Px→Pf(x)))
    
    // check whether we need to store alternatives for backtracking (only if
    // unifier affects variables on other open branches):
    var considerAlternatives = false;
    var unifier = unifiers[0], otherNode = otherNodes[0];
    VARLOOP: 
    for (var i=0; i<unifier.length; i+=2) {
        var variable = unifier[i];
        for (var j=0; j<this.tree.openBranches.length; j++) {
            var branch = this.tree.openBranches[j];
            if (branch != this && branch.freeVariables.includes(variable)) {
                considerAlternatives = true;
                break VARLOOP;
            }
        }
    }
    if (considerAlternatives) {
        for (var i=1; i<unifiers.length; i++) {
            var altTree = this.tree.copy();
            log("processing and storing alternative unifier for "+node+": "+unifiers[i]);
            // applying a substitution can make other branches closable as well
            altTree.applySubstitution(unifiers[i]);
            altTree.closeCloseableBranches();
            log('alternative tree:\n'+altTree);
            if (altTree.openBranches.length == 0) {
                // xxx what if we're currently adding the first node of a beta
                // expansion? Won't the tree miss the second node? 
                log('alternative tree closes, stopping proof');
                this.tree.prover.tree = altTree;
                return true;
            }
            this.tree.prover.alternatives.push(altTree);
        }
        if (this.todoList.length) {
            // instead of unifying, we could apply some other rule from the todoList:
            var altTree = this.tree.copy();
            log("storing non-unified alternative"); 
            // altTree is not unified, nextStep will apply next rule(s) 
            this.tree.prover.alternatives.push(altTree);
        }
        log(this.tree.prover.alternatives.length+' alternatives');
    }
    else {
        log("no need to consider alternatives for backtracking");
    }
    log("applying unifier for "+node+" and "+otherNode+": "+unifier);
    this.tree.applySubstitution(unifier);
    this.tree.closeBranch(this, node, otherNode);
    log(this.tree);
    log("+++ branch closed +++");
    return true;
}

Branch.prototype.copy = function() {
    // returns a copy of this branch with the same (===) nodes, for beta
    // expansions
    var nb = new Branch(this.tree,
                        this.nodes.copy(), // Array.copy
                        this.literals.copy(),
                        this.freeVariables.copy(),
                        this.skolemSymbols.copy(),
                        this.todoList.copyDeep(), // make copies of the todo items
                        this.closed);
    // disabled Herbrand restriction:
    //
    // for (var i=0; i<nb.unexpanded.length; i++) {
    //  if (nb.enexpanded[i].numExpansions) nb.unexpanded[i].numExpansions[nb.id] = nb.unexpanded[i].numExpansions[this.id];
    // }
    return nb;
}


Branch.prototype.addNode = function(node) {
    var doExpand = true;
    if (this.containsFormula(node.formula)) {
        // don't add node if same formula is already on branch, except if the
        // node comes from an alpha or beta expansion, in which case we
        // shouldn't call expandTodolist.
        if (node.fromRule == Prover.alpha || node.fromRule == Prover.beta) {
            doExpand = false;
        }
        else {
            return null;
        }
    }
    this.nodes.push(node);
    this.tree.numNodes++;
    if (node.type == 'literal') {
        this.literals.push(node);
    }
    if (!this.closed && doExpand) {
        this.expandTodoList(node);
    }
    // so that we can later find nodes added in the same step:
    node.expansionStep = this.tree.prover.step;
    return node;
}

Branch.prototype.containsFormula = function(formula) {
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].formula.string == formula.string) return true;
    }
    return false;
}


Branch.prototype.expandTodoList = function(node) {
    // insert node expansion into branch's todoList
    if (node.type != 'literal') {
        //
        // (We could use more clever heuristics about the order in which nodes
	// are expanded, e.g. look-ahead heuristics for beta expansions.  Turns
	// out that most of these don't have any consistent effect; they usually
	// speed up some proofs and slow down others.)
        //
        // TODO: check if it helps to favour beta applications for which the
	// complement of beta1 or beta2 is already on the branch (so that one of
	// the new branches will immediately close).
        //
        // TODO: One should never expand a beta node if either beta1 or beta2 is
        // already on the branch: if the resulting branches
        //
        // ... beta ... beta1 ... beta1 ...
        // ... beta ... beta1 ... beta2 ...
        //
        // both close, then so does
        //
        // ... beta ... beta1 ... 
        //
        // with beta unexpanded. Perhaps this could be handled in the code that
        // checks if a newly added formula already occurs on the branch.
        //
        var expansionRule = node.getExpansionRule();
	for (var i=0; i<this.todoList.length; i++) {
	    if (expansionRule.priority <= this.todoList[i][0].priority) break;
            // '<=' is important so that new gamma nodes are processed before old ones
	}
	this.todoList.insert([expansionRule, node], i);
    }
    if (this.tree.parser.isModal) {
        // Whenever a new world is first mentioned on a branch, rules like
        // seriality, transitivity etc. can potentially be applied with that
        // world. So we add these rules to todoList. 
        // symmetry can also be applied if vRu is first added for old worlds!
        if (this.nodes.length == 1) {
            // add accessibility rules for initial world:
            this.addAccessibilityRuleApplications();
        }
        else if (node.formula.predicate == this.tree.parser.R) {
            // node has form vRu; check that world u is new:
            // var worldName = node.formula.terms[1];
            // for (var i=0; i<this.nodes.length-1; i++) {
            //     if (node.formula.constants.includes(worldName)) {
            //         // xxx check that worldName is always a constant, not a
            //         // genuine skolem function
            //         return;
            //     }
            // }
            this.addAccessibilityRuleApplications(node);
        }
    }
}

Branch.prototype.addAccessibilityRuleApplications = function(node) {
    // Whenever a new world is first mentioned on a branch, rules like
    // seriality, transitivity etc. can potentially be applied with that
    // world. So we add these rules to todoList.
    for (var i=0; i<this.tree.prover.accessibilityRules.length; i++) {
        var rule = this.tree.prover.accessibilityRules[i];
        for (var j=0; j<this.todoList.length; j++) {
            if (rule.priority <= this.todoList[j][0].priority) break;
        }
        if (node) this.todoList.insert([rule, node], j);
        else this.todoList.insert([rule], j);
    }
}


Branch.prototype.merge = function() { // xxx remove?
    // If (the set of formulas on) a branch A is a subset of a branch B, then
    // only branch A needs to be checked, whereas B can be regarded as if it was
    // closed. (For if A closes, B closes as well, and if A doesn't close, the
    // search is over.) I check if it has become a branch B of this kind. If so,
    // it is removed from the tree. (This function can't be called directly from
    // addNode as that messes up the beta expansion).
    var branches = this.tree.closedBranches.concat(this.tree.openBranches);
    for (var i=0; i<branches.length; i++) {
        if (branches[i] == this) continue;
        var merge = true;
        nodeLoop:
        for (var j=0; j<branches[i].nodes.length; j++) {
            for (var k=0; k<this.nodes.length; k++) {
                if (this.nodes[k].formula.equals(branches[i].nodes[j].formula)) continue nodeLoop;
            }
            // log("can't merge "+this.nodes+" with "+branches[i].nodes+" because of "+branches[i].nodes[j]);
            merge = false;
            break;
        }
        if (merge) {
            log(this.tree);
            log("Merging: removing " + this.nodes + " from tree as it contains " + branches[i].nodes);
            if (!this.tree.mergedBranches) this.tree.mergedBranches = [];
            this.tree.mergedBranches.push(this);
            this.mergedWith = branches[i];
            this.mergePoint = branches[i].nodes[branches[i].nodes.length-1];
            this.tree.openBranches.remove(this);
            return 1;
        }
    }
    return 0;
}

Branch.prototype.toString = function() {
    return this.nodes.map(function(n){ return n.formula.string }).join(',');
}


function Node(formula, fromRule, fromNodes) {
    // Each non-initial node on a branch is the result of applying a rule to
    // (zero or more) earlier nodes on the same branch. This information about a
    // node's origin is needed to display the final sentence tableau, and for
    // pruning branches (see pruneBranch).
    if (!formula) return;
    this.formula = formula;
    this.fromRule = fromRule || null;
    this.fromNodes = fromNodes || [];
    this.type = formula.type;
    this.id = Node.counter++;
}
Node.counter = 0;

Node.prototype.getExpansionRule = function() {
    // return rule for expanding this node
    return Prover[this.type];
}


Node.prototype.iterateOverOrigin = function(iterFun) {
    // apply <iterFun> to this node and all its ancestors, in terms of rule
    // applications xxx remove
    var ancestor, ancestors = [this];
    while ((ancestor = ancestors.shift())) {
        iterFun(ancestor);
        for (var i=0; i<ancestor.fromNodes.length; i++) {
            if (!ancestors.includes(ancestor.fromNodes[i])) {
                ancestors.push(ancestor.fromNodes[i]);
            }
        }
    }
}

Node.prototype.toString = function() {
    return this.formula.string;
}


