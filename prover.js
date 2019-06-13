//
// This is where a free-variable tableaux are created.
//
// The 'prover' object has the following methods:
//
//    start(formula)         initiates the search
//    stop()                 halts the search
//    status(str)            takes status messages (to be overwritten)
//    finished(treeClosed)   is called when search is over (to be overwritten)
//    nextStep()             continues the search
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
//
// The tableaux created by the prover are instances of
//
//    Tree(rootFormula)
//
// with methods
//
//    closeBranch(branch, n1, n2)   clean up when a branch is closed
//    copy()                        make a deep copy to store for backtracking
//    applySubstitution(s)                 substitute terms (for unification) on the tree
//
// and properties
//
//    rootFormula       the formula on the root node
//    rootNode          the root node (see below)
//    openBranches      array of open branches
//    closedBranches    array of closed branches
//
// A branch is an instance of
//
//    Branch(tree, nodes, unexpanded, literals, freeVariables, constants)
//
// with properties (also optional constructor arguments)
//
//    nodes             array of nodes on the branch (see below)
//    unexpanded        array of unexpanded nodes, serves as todo list
//    literals          array of literal nodes (atomic formulas or negated atoms)
//    freeVariables     array of free variable on the branch
//    constants         array of constants on the branch
//
// and methods
//
//    expand()      expand the next formula on the branch
//    copy()        copies the branch (for BETA expansions)
//    merge()       deletes other branches if they are subsumed by this branch
//
// Finally, nodes are instances of
//
//    Node(formula, developedFrom)
//
// with properties
//
//    formula           the formula on the node
//    developedFrom     the node from which this one was developed
//
// and method
//
//    getSubNode(subIndex)
//
// which returns ALPHA_subIndex for ALPHA nodes or BETA_subindex for
// BETA nodes.
//
// While searching for a free variable tableaux, the prover also
// searches for a countermodel to the given formula. This is done by
// an instance of
//
//    ModelFinder(formula)
//
// which works independently of the tableau process by stupidly trying
// out all possible interpretations on the formula, starting with
// 1-element domains and adding more elements when all possible
// interpretations have been checked. (Realistically, it hardly ever
// gets to check interpretations with more than 5 or 6 individuals.)
//
// Methods:
//
//    isModel()  returns true if the current model satisfies the formula
//               (formula is handed to the constructor) 
//
//    search(n)  checks the next n models
//
// Property:
//
//    model    an object representing the currently tried model.
//             Its toString() method returns a HTML table showing the model


function Prover(initFormulas) {
////////////////////////////////////////// don't add nodes twice!!!

    this.depthLimit = 1; // depth = number of free variables on Tree
    this.nodeLimitFactor = 4;
    // depthLimit * nodeLimitFactor is the upper bound for number of
    // nodes on a branch before backtracking; value empirically chosen
    
    log("initializing prover");

    this.initFormulas = [];
    for (var i=0; i<initFormulas.length; i++) {
        this.initFormulas.push(initFormulas[i].normalize());
    }
    this.steps = 0;
    this.alternatives = [];
    this.tree = new Tree(this);
    this.rules = [Prover.alpha, Prover.beta, Prover.delta, Prover.gamma];
    this.modelFinder = new ModelFinder(this.initFormulas);
    this.counterModel = null;
    this.pauseLength = 2; // ms

    this.start = function() {
        this.nextStep();
    };

    this.stop = function() {
        this.stopTimeout = true;
        this.status("Proof halted");
    },

    this.status = function() {
        // to be overwritten
    }
    
    this.onfinished = function(state) { // state 1 = proved, 0 = proof failed
        log('proof completed');
        // to be overwritten
    }

}

Prover.prototype.nextStep = function() {
    // expands the next node on the present tree; then initializes backtracking
    // if limit is reached and occasionally searches for a countermodel; calls
    // itself again unless proof is complete.
    this.steps++;
    log('step ' + this.steps + ". " + this.tree.openBranches);
    
    // status msg: xxx tidy up
    var numBranches = this.tree.openBranches.length + this.tree.closedBranches.length;
    this.status("step " + this.steps + ": " + numBranches + " branches, " +
                this.tree.numNodes + " nodes, " +
                this.alternatives.length + " alternatives, search depth " +
                this.depthLimit);
        
    var newNodes;
    // expand leftmost open branch on tree:
    for (var i=0; i<this.rules.length; i++) {
        // result is list of changed nodes, or false if rule can't be applied
        // xxx optimise? instead of a lexical ordering, we might want to have a
        // priority ranking for different applications of the rules?
        newNodes = this.rules[i](this.tree.openBranches[0]);
        if (newNodes) break;
    }
    log(this.tree);
    var openBranches = this.tree.openBranches.copy();
    // try closing branch(es) with new nodes; new nodes are either on branch 0
    // or on neighbouring branches, after beta expansion
    if (newNodes) {
        for (var k=0; k<openBranches.length; k++) {
            var branch = openBranches[k];
            var branchChanged = false;
            for (var j=branch.nodes.length-1; j>=0; j--) {
                if (!newNodes.includes(branch.nodes[j])) break;
                branchChanged = true;
                var closed = branch.tryClose(branch.nodes[j]);
                // note that this might close all branches, through unification!
                if (this.tree.openBranches.length == 0) {
                    // no more open branches: proof completed
                    log('tree closed');
                    return this.onfinished(1);
                }
                if (closed) break;
            }
            if (!branchChanged) break;
        }
        // some branch still open
        if (this.tree.openBranches[0].nodes.length > this.depthLimit * this.nodeLimitFactor) {
            log('reached complexity limit for backtracking');
            this.limitReached();
        }
    }
    else {
        // no more rules can be applied
        log('tree open and complete');
        return this.onfinished(0);
    }
    
    // search for a countermodel:
    var counterModel = this.modelFinder.tryNextModel();
    if (counterModel) {
        this.counterModel = counterModel;
        return this.onfinished(0);
    }
    
    if (this.steps % 20 == 19) {
        // Often, there are thousands of trees to check with depth n, and none
        // of them closes, whereas many close for n+1. Changing the depth
        // measure doesn't change this. Instead, once every x steps, we increase
        // the limit for a while and then reset it:
        if (this.steps % 1000 == 999) {
            log("trying with increased depth for a few steps");
            this.depthLimit++;
            this.decreaseLimit = this.steps + 200;
        }
        else if (this.steps == this.decreaseLimit) {
            log("resetting depth");
            this.depthLimit--;
        }
    }
    
    if (this.stopTimeout) {
        // proof manually interrupted
        this.stopTimeout = false;
    }
    else if (this.pauseLength) {
        // continue with next step after short break to display status message
        // and not get killed by browsers
        setTimeout(function(){
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

Prover.alpha = function(branch) {
    // xxx optimize! if a branch contains lots of unexpanded non-alpha nodes, we
    // go through them after each application of any rule, testing if alpha() is
    // applicable. Should only test newly added nodes, or store unexpanded_alpha
    // etc. (with num_unexpanded to quickly see if any left)?
    for (var i=0; i<branch.unexpanded.length; i++) {
        var node = branch.unexpanded[i];
        if (node.type == 'alpha') { // xxx better is_alpha?
            branch.unexpanded.remove(node); // xxx optimise?
            return [branch.addNode(node.getSubNode(2)),
                    branch.addNode(node.getSubNode(1))];
        }
    }
    return null;
}

Prover.beta = function(branch) {
    for (var i=0; i<branch.unexpanded.length; i++) {
        var node = branch.unexpanded[i];
        if (node.type == 'beta') {
            branch.unexpanded.remove(node);
            branch.tree.openBranches.unshift(branch.copy());
            var n1 = branch.tree.openBranches[0].addNode(node.getSubNode(1));
            var n2 = branch.addNode(node.getSubNode(2));
            return [n1,n2];
        }
    }
    return null;
}

Prover.gamma = function(branch) {
    for (var i=0; i<branch.unexpanded.length; i++) {
        var node = branch.unexpanded[i];
        if (node.type == 'gamma') { 
            if (branch.freeVariables.length == this.depthLimit) {
                log("depthLimit " + this.depthLimit + " exceeded!");
                this.limitReached();
                return null;
            }
            branch.unexpanded.remove(node);
            branch.unexpanded.push(node);
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
            var newVariable = branch.newVariable();
            branch.freeVariables.push(newVariable);
            var newFormula = node.formula.matrix.substitute(node.formula.variable, newVariable);
            var newNode = new Node(newFormula, node);
            newNode.instanceTerm = newVariable;
            return [branch.addNode(newNode)];
        }
    }
}

Prover.delta = function(branch) {
    for (var i=0; i<branch.unexpanded.length; i++) {
        var node = branch.unexpanded[i];
        if (node.type == 'delta') { 
            // find skolem term (newTerm):
            var funcSymbol = branch.newFunctionSymbol();
            branch.constants.push(funcSymbol);
            // It suffices to skolemize on variables contained in this formula.
            // This makes some proofs much faster by making some gamma
            // applications redundant. However, translation into sentence
            // tableau then becomes almost impossible, because here we need the
            // missing gamma applications. Consider Ax(Fx & Ey~Fy).
            if (branch.freeVariables.length > 0) {
                var skolemTerm = branch.freeVariables.copy();
                skolemTerm.unshift(funcSymbol);
            }
            else skolemTerm = funcSymbol;
            var newFormula = node.formula.matrix.substitute(node.formula.variable, skolemTerm);
            var newNode = new Node(newFormula, node);
            newNode.instanceTerm = skolemTerm;
            branch.unexpanded.remove(node); 
            return [branch.addNode(newNode)];
        }
    }
    return null;
}


function Tree(prover) {
    if (!prover) return; // for copy() function
    this.prover = prover;
    var initBranch = new Branch(this);
    initBranch.constants = []; // for run-time skolemization
    for (var i=0; i<prover.initFormulas.length; i++) {
        var formula = prover.initFormulas[i];
        var node = new Node(formula);
        initBranch.addNode(node);
        initBranch.constants = initBranch.constants.concat(formula.constants); // xxx optimise! (no duplicates)
    }
    this.openBranches = [initBranch];
    this.closedBranches = [];
    this.numNodes = 0;
}

Tree.prototype.closeBranch = function(branch, complementary1, complementary2) {
    this.pruneBranch(branch, complementary1, complementary2);
    this.pruneAlternatives();
    this.openBranches.remove(branch);
    this.closedBranches.push(branch);
}

Tree.prototype.pruneAlternatives = function() {
    // discard all alternatives whose open branches are a superset of
    // this.openBranches; otherwise a lot of time is spent in complex proofs
    // exploring alternatives that reopen already closed branches without making
    // progress on open ones.
    var alternatives = this.prover.alternatives.copy();
    ALTLOOP:
    for (var i=0; i<alternatives.length; i++) {
        var altTree = alternatives[i];
        for (var j=0; j<this.openBranches.length; j++) {
            var openBranch = this.openBranches[j];
            if (!altTree.containsOpenBranch(openBranch)) { // xxx optimise: containsopenbranch looks through all open branches for each call
                log('alternative '+i+' does not contain open branch '+openBranch);
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
    
Tree.prototype.pruneBranch = function(branch, complementary1, complementary2) {
    // When a branch is closed, we look for beta expansions on it that weren't
    // used to derive the complementary pair (nor any complementary pair of an
    // already closed subbranch); all branches originating from unused beta
    // expansions can be removed.
    for (var n=complementary1; n; n=n.developedFrom) n.used = true;
    for (var n=complementary2; n; n=n.developedFrom) n.used = true;
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
    // return a deep copy including copy of nodes
    var ntree = new Tree();
    var nodemap = {} // old node id => copied Node
    ntree.prover = this.prover
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
    
    function copyNode(orig) {
        if (nodemap[orig.id]) return nodemap[orig.id];
        var n = new Node();
        n.formula = orig.formula;
        if (orig.developedFrom) {
            if (!nodemap[orig.developedFrom.id]) {
                throw "from node "+orig.developedFrom+" not yet copied";
            }
            n.developedFrom = nodemap[orig.developedFrom.id];
        }
        n.type = orig.type;
        n.used = orig.used;
        n.id = orig.id;
        n.instanceTerm = orig.instanceTerm;
        nodemap[orig.id] = n;
        return n;
    }
    function copyBranch(orig) {
        var nodes = [];
        var unexpanded = [];
        var literals = [];
        for (var i=0; i<orig.nodes.length; i++) {
            nodes.push(copyNode(orig.nodes[i]));
        } 
        for (var i=0; i<orig.unexpanded.length; i++) {
            unexpanded.push(nodemap[orig.unexpanded[i].id]);
        } 
        for (var i=0; i<orig.literals.length; i++) {
            literals.push(nodemap[orig.literals[i].id]);
        } 
        var b = new Branch(ntree, nodes, unexpanded, literals, orig.freeVariables.copy(), orig.constants);
        b.id = orig.id;
        return b;
    }
    return ntree;
}

Tree.prototype.genericcopy = function() {
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

function Branch(tree, nodes, unexpanded, literals, freeVariables, constants) {
    this.tree = tree;
    this.nodes = nodes || [];
    this.unexpanded = unexpanded || [];
    this.literals = literals || [];
    this.freeVariables = freeVariables || [];
    this.constants = constants || [];
    this.id = Branch.counter++;
}
Branch.counter = 0;

Branch.prototype.newVariable = function() {
    // return new variable for gamma expansion
    if (this.freeVariables.length == 0) {
        return 'ξ1';
    }
    var lastvar = this.freeVariables[this.freeVariables.length-1]
    return 'ξ'+(lastvar.substr(1)*1+1);
}

Branch.prototype.newFunctionSymbol = function() {
    // return new function symbol for delta expansion
    if (this.constants.length == 0) {
        return 'φ1';
    }
    // xxx optimise!
    for (var i=this.constants.length-1; i>=0; i--) {
        if (this.constants[i][0] == 'φ') return 'φ'+(this.constants[i].substr(1)*1+1);
    }
    return 'φ1';
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
    if (node.type != 'literal') return false;
    // Formula.unify() only works for literals  
    var unifiers = [];
    var otherNodes = [];
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
    // xxx todo: use simpler unifiers first?
    
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
            // have to close the correct branch on altTree with the correct pair
            // of nodes (that branch isn't <this> and the nodes aren't <node>
            // and <oNode>):
            // var altBranch = altTree.openBranches[0], altNode, altONode;
            // for (var j=0; j<altBranch.literals.length; j++) {
            //     if (altBranch.literals[j].formula.equals(node.formula)) {
            //         altNode = altBranch.literals[j];
            //     }
            //     else if (altBranch.literals[j].formula.equals(oNode.formula)) {
            //         altONode = altBranch.literals[j];
            //     }
            // }
            // applying a substitution can make other branches closable as well
            altTree.applySubstitution(unifiers[i]);
            // altTree.closeBranch(altBranch, altNode, altONode);
            altTree.closeCloseableBranches();
            log(altTree);
            if (altTree.openBranches.length == 0) {
                log('alternative tree closes, stopping proof');
                this.tree.prover.tree = altTree;
                return true;
            }
            this.tree.prover.alternatives.push(altTree);
            log(this.tree.prover.alternatives.length+' alternatives');
        }
        if (this.unexpanded.length) { // xxx doesn't check if non-expansion rules can be applied
            // instead of unifying, we could apply some expansion rule:
            var altTree = this.tree.copy();
            log("storing non-unified alternative (unexpanded " + this.unexpanded + ")"); 
            // altTree is not unified, nextStep will apply next rule(s) 
            this.tree.prover.alternatives.push(altTree);
            log(this.tree.prover.alternatives.length+' alternatives');
        }
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
                        this.unexpanded.copy(),
                        this.literals.copy(),
                        this.freeVariables.copy(),
                        this.constants.copy());
    // disabled Herbrand restriction
    //
    // for (var i=0; i<nb.unexpanded.length; i++) {
    //  if (nb.unexpanded[i].numExpansions) nb.unexpanded[i].numExpansions[nb.id] = nb.unexpanded[i].numExpansions[this.id];
    // }
    return nb;
}


Branch.prototype.addNode = function(node) {
    // xxx check if node is already on branch?
    this.nodes.push(node);
    this.tree.numNodes++;
    if (node.type == 'literal') this.literals.push(node);
    else this.unexpanded.unshift(node); // new gamma nodes should be processed before old ones
    return node;
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
    return "[Unexpanded: " + this.unexpanded + " Literals: " + this.literals + "]";
}


function Node(formula, developedFrom) {
    if (!formula) return;
    this.formula = formula;
    this.developedFrom = developedFrom || null;
    this.type = formula.type;
    this.id = Node.counter++;
}
Node.counter = 0;

Node.prototype.getSubNode = function(subIndex) {
    var subfla = subIndex == 1 ? this.formula.sub1 : this.formula.sub2;
    return new Node(subfla, this);
}

Node.prototype.toString = function() {
    return this.formula.string;
}


function ModelFinder(initFormulas) {
    log("Creating ModelFinder");
    
    this.initFormulas = initFormulas;
    this.signature = initFormulas[0].signature; // this takes all initFormulas into account
    this.constants = [];
    this.predicates = [];
    for (var i=0; i<initFormulas.length; i++) {
        var cs = initFormulas[i].constants;
        for (var j=0; j < cs.length; j++) {
            if (!this.constants.includes(cs[j])) this.constants.push(cs[j]);
        }
        var ps = initFormulas[i].predicates;
        for (var j=0; j<ps.length; j++) {
            if (!this.predicates.includes(ps[j])) this.predicates.push(ps[j]);
        }
    }
    
    this.model = new Model(this);
    
} 

ModelFinder.prototype.tryNextModel = function() {
    if (this.model.domain.length == 0) this.model.initInterpretation(1);
    else this.model.iterate();
    log("trying model "+this.model);
    if (this.isModel(this.model)) return this.model;
    return null;
} 

ModelFinder.prototype.isModel = function(model) {
    for (var i=0; i<this.initFormulas.length; i++) {
        if (!this.model.satisfies(this.initFormulas[i])) {
            log("no, model doesn't satisfy "+this.initFormulas[i].string);
            return false;
        }
    }
    log("yep, model satisfies initFormulas");
    return true;
}

function Model(modelfinder) {
    this.domain = [];
    this.argLists = [];
    this.values = [];
    this.symbols = modelfinder.predicates.concat(modelfinder.constants);
    this.isPredicate = [];
    for (var i=0; i<modelfinder.predicates.length; i++) {
        this.isPredicate[modelfinder.predicates[i]] = true;
    }
    this.signature = modelfinder.signature;
}

Model.prototype.initInterpretation = function(numIndividuals) {
    // JS doesn't allow lists as dict keys. Since the keys only need to be
    // generated once for every domain, it's not too inefficient to convert them
    // to strings.
    //
    // For the next iteration, we can simply permute the list of /outputs/.
    // In fact, we wouldn't even need to store the keys. It's clear what they
    // are anyway given arity and numIndividuals. We really only need to store
    // the output sequence in order of the argument permutations.
    //
    // So let's have a genuine interpretation function getValue that takes a
    // symbol and a tuple of individuals [0,1] as argument, computes the
    // position of the tuple in the list of all 2-ary tuples of individuals, and
    // returns that position from the values array.
    //
    // So we store values[f] = [0,0,1,0,...], values[F] = [true, false, ...],
    // where values[f][0] is the value of f for the first tuple, etc.
    //
    // For zero-ary predicates and functors/constants, there is only one
    // possible argument list: the empty list. It's more efficient to store
    // values[a] = 0, values[p] = true, bypassing the arrays.
    this.domain = [];
    for (var i=0; i<numIndividuals; i++) {
        this.domain.push(i); // domain is integers 0,1,...
    }
    this.argLists = []; // stores all possible arguments for all arities, as strings
    this.values = {};
    for (var i=0; i<this.symbols.length; i++) {
        var sym = this.symbols[i];
        var arity = this.signature.arities[sym];
        if (arity == 0) {
            this.values[sym] = 0; // false or 1st individual
            continue;
        }
        if (!this.argLists[arity]) {
            this.argLists[arity] = initArguments(arity);
        }
        this.values[sym] = Array.getArrayOfZeroes(this.argLists[arity].length); // note that false == 0
        // this.values[f] is the list of values corresponding to the argument
        // tuples in argLists[arity]
    }
    
    function initArguments(arity) {
        // set up this.argLists[arity] as list of all tuples from this.domain,
        // with length <arty>, as strings.
        var res = [];
        var tuple = Array.getArrayOfZeroes(arity);
        res.push(tuple.toString());
        while (Model.iterateTuple(tuple, numIndividuals-1)) { // optimise?
            res.push(tuple.toString());
        }
        return res;
    }
    
}

Model.iterateTuple = function(tuple, maxValue) {
    // changes tuple to the next tuple in the list of the cartesian powers of
    // {0..maxValue} of arity <tuple>.length.
    for (var i=tuple.length-1; i>=0; i--) {
        if (tuple[i] < maxValue) {
            tuple[i]++;
            return true;
        }
        tuple[i] = 0;
    }
    return false;
    // Example 1: tuple = 011, maxValue = 2.
    //   at i=2, tuple -> 012, return true
    // Example 2: tuple = 011, maxValue = 1.
    //   at i=2, tuple -> 010
    //   at i=1, tuple -> 000
    //   at i=0, tuple -> 100, return true
}

Model.prototype.getValue = function(symbol, args) {
    if (!args || args.length == 0) { // zero-ary proposition letter or ind constant
        return this.values[symbol];
    }
    var arity = args.length;
    var argsIndex = this.argLists[arity].indexOf(args.toString()); // optimise?
    return this.values[symbol][argsIndex];
}

Model.prototype.iterate = function() {
    // change this model to the next possible model.
    //
    // We need to change one thing at a time. E.g., if we have F and f, we need
    // to iterate through all possible values for f for all possible values
    // for F.
    for (var i=0; i<this.symbols.length; i++) {
        var sym = this.symbols[i];
        var maxValue = this.isPredicate[sym] ? 1 : this.domain.length-1;
        if (!this.values[sym].isArray) { // zero-ary
            if (this.values[sym] < maxValue) {
                this.values[sym]++;
                return true;
            }
            else this.values[sym] = 0;
        }
        var iterated = Model.iterateTuple(this.values[sym], maxValue);
        if (iterated) return true;
        // Now reset interpretation of sym to zero and iterate interpretation of
        // next symbol; turns out iterateTuple already sets this.values[sym] to
        // zero if no iteration was possible. So nothing left to do.
    }
    // no iteration possible
    this.initInterpretation(this.domain.length+1);
    log('extending domain of modelfinder to '+this.domain);
}

Model.prototype.satisfies = function(formula) {
    // this could be sped up a lot xxx
    switch (formula.type) {
    case 'alpha' : return this.satisfies(formula.sub1) && this.satisfies(formula.sub2);
    case 'beta' : return this.satisfies(formula.sub1) || this.satisfies(formula.sub2);
    case 'gamma' : {
        for (var i=0; i<this.domain.length; i++) {
            this.values[formula.variable] = this.domain[i];
            var res = this.satisfies(formula.matrix);
            delete this.values[formula.variable]; // so that it's not printed by toString
            if (!res) return false;
        }
        return true;
    }
    case 'delta' : {
        for (var i=0; i<this.domain.length; i++) {
            this.values[formula.variable] = this.domain[i];
            var res = this.satisfies(formula.matrix);
            delete this.values[formula.variable]; // so that it's not printed by toString
            if (res) return true;
        }
        return false;
    }
    case 'literal' : {
        var fla = formula.sub || formula;
        var args = [];
        for (var i=0; i<fla.terms.length; i++) {
            args.push(this.interpretTerm(fla.terms[i]));
        }
        var val = this.getValue(fla.predicate, args);
        return formula.sub ? !val : val;
    }
    }
}

Model.prototype.interpretTerm = function(term) {
    if (term.isArray) {
        var funcsym = term[0];
        var args = [];
        for (var i=1; i<term.length; i++) {
            args.push(this.interpretTerm(term[i]));
        }
        return this.getValue(funcsym, args);
    }
    return this.getValue(term);
}

Model.prototype.toString = function() {
    var str = "<table>";
    str += "<tr><td>Domain: </td><td align='left'>{ ";
    str += this.domain.join(", ");
    str += " }</td></tr>";
    for (var i=0; i<this.symbols.length; i++) {
        var sym = this.symbols[i];
        // p: true
        // a: 0
        // F: { 0,1 }
        // G: { <0,0>, <1,1> }
        // f: { <0,1>, <1,1> }
        if (!this.values[sym].isArray) { // zero-ary
            val = this.values[sym];
        }
        else {
            var ext = [];
            var arity = this.signature.arities[sym];
            for (var j=0; j<this.argLists[arity].length; j++) {
                if (this.isPredicate[sym]) {
                    if (this.values[sym][j]) { // argLists[arity][j] is in extension of sym
                        if (arity == 1) {
                            ext.push(this.argLists[arity][j].slice(1,-1)); // remove brackets
                        }
                        else {
                            ext.push('&lt;'+this.argLists[arity][j].slice(1,-1)+'&gt;');
                        }
                    }
                }
                else { // functor
                    ext.push('&lt;'+this.argLists[arity][j].slice(1,-1)+','+this.values[sym][j]+'&gt;');
                }
            }
            val = '{ '+ext.toString().slice(1,-1)+' }';
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>";
    }
    str += "</table>";
    return str;
}
