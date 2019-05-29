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
//    closeBranch(branch, c1, c2)   clean up when a branch is closed
//    copy()                        make a deep copy to store for backtracking
//    substitute(s)                 substitute terms (for unification) on the tree
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
//    unexpanded        array of unexpanded nodes
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

tc.register("LITERAL");
tc.register("ALPHA");
tc.register("DELTA");
tc.register("BETA");
tc.register("GAMMA");

prover = {
    debug : true,
    nodeLimitFactor : 4,
    // depthLimit * nodeLimitFactor is the upper bound for number of
    // nodes on a branch; value empirically chosen
    
    start : function(formula) {
        debug("initializing prover with " + translator.fla2html(formula));
        this.formula = formula;
        this.depthLimit = 1; // depth = number of free variables on Tree
        this.limitReached = false;
        this.steps = 0;
        this.alternatives = [];
        this.tree = new Tree(formula);
        this.modelFinder = new ModelFinder(formula);
        this.counterModel = null;
        this.nextStep();
    },

    stop : function() {
        this.stopTimeout = true;
        this.status("Proof halted");
    },

    status : function(str) {
    },

    finished : function(state) { // state 1 = proved, 0 = proof failed
    },
    
    nextStep : function() {
        // expands the next node on the present tree; then initializes
        // backtracking if limit is reached and occasionally searches
        // for a countermodel; calls itself again unless proof is
        // complete.
        this.steps++;
        debug(this.steps + ". " + this.tree.openBranches);
        
        // status msg:
        var numBranches = this.tree.openBranches.length + this.tree.closedBranches.length;
        this.status("step " + this.steps + ": " + numBranches + " branches, " +
                    this.tree.numNodes + " nodes, " +
                    this.alternatives.length + " alternatives, search depth " +
                    this.depthLimit);
        
        // expand tree:
        var result = this.tree.openBranches[0].expand();
        debug(this.tree);
        if (result == 1) { // branch closed
            if (this.tree.openBranches.length == 0) {
                // no open branches: proof completed
                return this.finished(1);
            }
        }
        else if (result == 0) { // branch still open
            if (this.tree.openBranches[0].nodes.length > this.depthLimit * this.nodeLimitFactor) {
                this.limitReached = true;
                this.backtrack();
            }
        }
        else { // result == -1 means branch cannot be closed:
            return this.finished(0);
        }

        if (this.steps % 20 == 19) {
            // search for a countermodel:
            debug("searching for countermodel");
            var counterModel = this.modelFinder.search(10);
            if (counterModel) {
                this.counterModel = counterModel;
                return this.finished(0);
            }
            
            // Often, there are thousands of trees to check with depth
            // n, and none of them closes, whereas many close for n+1.
            // Changing the depth measure doesn't change this.
            // Instead, once every x steps, we increase the limit for
            // a while and then reset it:
            if (this.steps % 1000 == 999) {
                debug("trying with increased depth for a few steps");
                this.depthLimit++;
                this.decreaseLimit = this.steps + 200;
            }
            else if (this.steps == this.decreaseLimit) {
                debug("resetting depth");
                this.depthLimit--;
            }
        }
        
        if (this.stopTimeout) {
            // proof manually interrupted
            this.stopTimeout = false;
        }
        else {
            // continue with next step after short break to display
            // status message and not get killed by browsers
            setTimeout("prover.nextStep()", this.debug ? numBranches*100 : numBranches*5);
        }

    },
    
    backtrack : function() {
        // called in different ways...
        if (this.alternatives.length == 0) {
            // no alternative trees to explore
            if (!this.limitReached) {
                // we haven't reached the depthLimit previously, so
                // it's no use increasing it: proof has failed
                debug("backtracking impossible");
                return false;
            }
            // start over with increased depth limit
            this.depthLimit++;
            debug("----- increasing depthLimit to " + this.depthLimit + " -----");
            this.tree = new Tree(this.formula);
            this.limitReached = false;
            return true;
        }
        debug(" * Backtracking * ");
        this.tree = this.alternatives.shift();
        return true;
    }
}


function Tree(rootFormula) {
    if (!rootFormula) return; // for copy() function
    if (!rootFormula.normalized) {
        rootFormula.normalized = rootFormula.normalize();
        debug("normalizing: " + translator.fla2html(rootFormula.normalized));
    }
    this.rootFormula = rootFormula;
    this.firstNewVariable = 3; // so that we don't use variables as
                               // free variables that already occur in
                               // formulas and might get captured
    var vars = rootFormula.normalized.getBoundVariables();
    for (var i=0; i<vars.length; i++) {
        if (vars[i] >= this.firstNewVariable) {
            this.firstNewVariable = vars[i] + 3;
        }
    }
    var consts = rootFormula.normalized.getConstants();
    consts.sort(function(a,b){ return a-b });
    this.rootNode = new Node(rootFormula.normalized);
    this.openBranches = [new Branch(this, [this.rootNode], [this.rootNode], [], [], consts)];
    this.closedBranches = [];
    this.numNodes = 0;
}

Tree.prototype.closeBranch = function(branch, complementary1, complementary2) {
    // Pruning: When a branch is closed, we look for beta expansions
    // on it that weren't used to derive the complementary pair (nor
    // any complementary pair of an already closed subbranch).
    // All branches originating from unused beta expansions can
    // be removed.
    for (var n=complementary1; n; n=n.developedFrom) n.used = true;
    for (var n=complementary2; n; n=n.developedFrom) n.used = true;
    toRoot:
    for (var i=branch.nodes.length-1; branch.nodes[i].developedFrom; i--) {
        if (branch.nodes[i].developedFrom.type != tc.BETA) continue;
        // if on a branch with nodes [n1,...,n17] BETA is applied, the
        // result are two branches [n1,...,n17,b1], [n1,...,n17,b2].
        // b1 and b2 have the same index.
        for (var j=0; j<this.openBranches.length; j++) {
            if (this.openBranches[j] == branch) continue;
            if (this.openBranches[j].nodes[i] &&
                this.openBranches[j].nodes[i].developedFrom == branch.nodes[i].developedFrom &&
                this.openBranches[j].nodes[i] != branch.nodes[i]) {
                // another open branch originating here
                if (branch.nodes[i].used) {
                    // can't look any further because from here
                    // upwards this subtree isn't closed
                    break toRoot;
                }
                debug("pruning branch "+this.openBranches[j]+" originating from unused node "+branch.nodes[i].developedFrom);
                this.openBranches.remove(this.openBranches[j]);
                // note that we don't remove the beta expansion result
                // on the closed branch.
                break;
            }
        }
    }
    this.openBranches.remove(branch);
    this.closedBranches.push(branch);
}

Tree.prototype.copy = function() {
    // return a deep copy down to the level of nodes
    var ntree = new Tree();
    ntree.rootFormula = this.rootFormula;
    ntree.firstNewVariable = this.firstNewVariable;
    var nodemap = {} // old node id => copied Node
    function copyNode(orig) {
        if (nodemap[orig.id]) return nodemap[orig.id];
        var n = new Node();
        n.formula = orig.formula;
        n.developedFrom = orig.developedFrom ? nodemap[orig.developedFrom.id] : null;
        n.type = orig.type;
        n.unifyWith = orig.unifyWith;
        n.complementary = orig.complementary;
        n.used = orig.used; // xxx what is this for?
        n.__markClosed = orig.__markClosed; // xxx dito 
        n.id = orig.id;
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
        var b = new Branch(ntree, nodes, unexpanded, literals, orig.freeVariables, orig.constants);
        b.id = orig.id;
        return b;
    }
    ntree.rootNode = copyNode(this.rootNode);
    ntree.openBranches = [];
    for (var i=0; i<this.openBranches.length; i++) {
        ntree.openBranches.push(copyBranch(this.openBranches[i]));
    }
    ntree.closedBranches = [];
    for (var i=0; i<this.closedBranches.length; i++) {
        ntree.closedBranches.push(copyBranch(this.closedBranches[i]));
    }
    ntree.numNodes = this.numNodes;
    return ntree;
}

Tree.prototype.copy = function() {
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

Tree.prototype.substitute = function(substitution) {
    var branches = this.openBranches.concat(this.closedBranches);
    for (var i=0; i<substitution.length; i+=2) {
        for (var b=0; b<branches.length; b++) {
            for (var n=0; n<branches[b].nodes.length; n++) {
                branches[b].nodes[n].formula.substitute(substitution[i], substitution[i+1]);
                // we don't need to do anythings with subNodeFlas or
                // matrix because their formula object is a (possibly
                // negated) subformula of this.formula. So any changes
                // to the terms in this.formula carries over to their
                // formula object.
            }
            branches[b].freeVariables.remove(substitution[i]);
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
            res += "<table><tr><td align='center' valign='top' style='font-family:monospace; border-top:1px solid #999; padding:3px; border-right:1px solid #999'>" + getTree(children[0], recursionDepth) + "</td>\n<td align='center' valign='top' style='padding:3px; border-top:1px solid #999; font-family:monospace'>" + getTree(children[1], recursionDepth) + "</td>\n</tr></table>";
        }
        else if (children[0]) res += getTree(children[0], recursionDepth);
        return res;
    }
}

function Branch(tree, nodes, unexpanded, literals, freeVariables, constants) {
    this.tree = tree;
    this.nodes = nodes;
    this.unexpanded = unexpanded;
    this.literals = literals || [];
    this.freeVariables = freeVariables || [];
    this.constants = constants || [];
    this.id = Branch.counter++;
}
Branch.counter = 0;

Branch.prototype.expand = function() {
    var node = this.unexpanded.shift();
    if (!node) {
        debug("*** branch remains open!"); 
        return prover.backtrack() ? 0 : -1;
    }
    switch (node.type) {
        case tc.ALPHA : {
            this.addNode(node.getSubNode(2));
            this.addNode(node.getSubNode(1));
            break;
        }
        case tc.BETA : {
            this.tree.openBranches.unshift(this.copy());
            this.tree.openBranches[0].addNode(node.getSubNode(1));
            this.addNode(node.getSubNode(2));
            // if (fastMode) this.tree.openBranches[0].merge();
            break;
        }
        case tc.GAMMA : {
            if (this.freeVariables.length == prover.depthLimit) {
                debug("depthLimit " + prover.depthLimit + " exceeded!");
                prover.limitReached = true;
                prover.backtrack(true);
                return 0;
            }
            // The following lines would incorporate the Herbrand restriction on sentence tableau: 
            // do not expand a gamma node more often than there are constants on the branch.
            // For this purpose, s(0) and s(s(0)) should count as different constants, but 
            // this.constants only contains [s,0], so I would have to keep track of the actual
            // instances somewhere. So for now, that's disabled. (2005-02-02) 
            // if (!node.numExpansions) node.numExpansions = [];
            // if (!node.numExpansions[this.id]) node.numExpansions[this.id] = 1;
            // else {
            //  node.numExpansions[this.id]++;
            //  if (node.numExpansions[this.id] > this.constants.length + 1) {
            //      debug("Branch unclosable by Herbrand restriction: " + node.numExpansions[this.id] + " expansions, " + this.constants.length + " constants on branch");
            //      // too many gamma instances. But not all is lost if we can backtrack:
            //      return prover.backtrack() ? 0 : -1;
            //  }
            //}
            var newVariable = this.freeVariables.length ? this.freeVariables[this.freeVariables.length-1] + 3 : this.tree.firstNewVariable;
            this.freeVariables.push(newVariable);
            var newFormula = node.formula[2].copyDeep().substitute(node.formula[1], newVariable);
            this.addNode(new Node(newFormula, node));
            this.unexpanded.push(node);
            break;
        }
        case tc.DELTA : {
            // find skolem term (newTerm):
            debug(this.constants);
            var newTerm = this.constants.length ? this.constants[this.constants.length-1] + 3 : 2;
            this.constants.push(newTerm);
            var freeVars = this.freeVariables.copy();
            // It suffices to skolemize on variables contained in this formula. This makes some proofs much faster. 
            // However, translation into sentence tableau then becomes almost impossible. Consider Ax(Fx & Ey~Fy).
            // var freeVars = node.formula.getFreeVariables();
            if (freeVars.length !== 0) {
                freeVars.unshift(newTerm);
                newTerm = freeVars;
            }
            var newFormula = node.formula[2].copyDeep().substitute(node.formula[1], newTerm);
            this.addNode(new Node(newFormula, node));
            break;
        }
        case tc.LITERAL : {
            // Now we face some choices: unify the literal or expand the next node in unexpanded?
            // And if unify, with which other formula? We try one option and store the others 
            // for backtracking. When backtracking for alternative unifiers, the literal will be 
            // met again, but then it will carry a flag "unifyWith" telling us with what it should 
            // be unified with.
            // If no unified variables occur on any other current branch, there is no point of 
            // exploring alternatives, as the unification will leave all other branches unchanged.
            var negatedFormula = (node.formula[0] == tc.NOT) ? node.formula[1] : node.formula.negate();
                        var unifier;
            if (!node.unifyWith) {
                if (this.literals.length == 0) { // unification impossible
                    this.literals.unshift(node);
                    return 0;
                }
                var unifyCandidates = [];
                for (var i=0; i<this.literals.length; i++) {
                    var unif = negatedFormula.unify(this.literals[i].formula);
                    if (unif.isArray) {
                        unifyCandidates.push(this.literals[i]);
                        if (!unifier) unifier = unif;
                    }
                }
                if (!unifier) { // unification impossible
                    this.literals.unshift(node);
                    return 0;
                }
                // we use the first one and store all other options for backtracking.
                // But first check whether backtracking is needed:
                var considerAlternatives = false;
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
                    for (var i=1; i<unifyCandidates.length; i++) {
                        this.unexpanded.unshift(node);
                        node.unifyWith = unifyCandidates[i];
                        prover.alternatives.unshift(this.tree.copy()); // copy must copy also the unifyWith property (as clone() of course does)
                        debug("storing alternative unifier: " + unifyCandidates[i]);
                        this.unexpanded.shift();
                    }
                    if (this.unexpanded.length) {
                        // instead of unifying, we could expand other nodes:
                        this.literals.unshift(node);
                        prover.alternatives.unshift(this.tree.copy());
                        debug("storing alternative expansions: " + this.unexpanded);
                        this.literals.shift();
                    }
                }
                else {
                    debug("no need to consider alternatives for backtracking");
                }
                node.unifyWith = unifyCandidates[0];
            }
            else unifier = negatedFormula.unify(node.unifyWith.formula);
            // now unify:
            debug("unifier for "+node+" and "+node.unifyWith+": "+unifier);
            this.tree.substitute(unifier);
            this.tree.closeBranch(this, node, node.unifyWith);
            node.complementary = node.unifyWith;
            node.unifyWith.complementary = node;
            debug("+++ branch closed +++");
            return 1; // job successfully completed and tableau branch closed
        }
    }
    return 0;
    // fastmode: return this.merge();
}

Branch.prototype.copy = function() {
    // mustn't use clone(), as that creates a clone even of this.tree (and of all the formulas, breaking merge()).
    var nb = new Branch(this.tree, this.nodes.copy(), this.unexpanded.copy(), this.literals.copy(), this.freeVariables.copy(), this.constants.copy());
    // disabled Herbrand restriction:
    // for (var i=0; i<nb.unexpanded.length; i++) {
    //  if (nb.unexpanded[i].numExpansions) nb.unexpanded[i].numExpansions[nb.id] = nb.unexpanded[i].numExpansions[this.id];
    // }
    return nb;
}


Branch.prototype.addNode = function(node) {
    // xxx check if node is already on branch?
    this.nodes.push(node);
    this.tree.numNodes++;
    // this.nexpanded is processed sequentially. So here we could make some clever decisions 
    // about the order in which formulas are expanded, e.g. look-ahead heuristics for beta expansions. 
    // Turns out that most of these don't have any significant effect; they usually speed up some
    // proofs and slow down others. What we do is insert ALPHA before BETA etc. (but even that 
    // has only a minor and partial benefit.)
    var order = {};
    order[tc.LITERAL] = 1; order[tc.ALPHA] = 2; order[tc.BETA] = 3; order[tc.DELTA] = 4; order[tc.GAMMA] = 5;
    var pos = 0;
    while (pos < this.unexpanded.length) {
        if (order[node.type] <= order[this.unexpanded[pos].type]) break;
        pos++;
    }
    this.unexpanded.insert(node, pos);
    // this.unexpanded.unshift(node);
}

Branch.prototype.merge = function() {
    // If (the set of formulas on) a branch A is a subset of a branch B, then only
    // branch A needs to be checked, whereas B can be regarded as if it was
    // closed. (For if A closes, B closes as well, and if A doesn't close, the
    // search is over.)
    // I check if it has become a branch B of this kind. If so, it is removed from the tree. 
    // (This function can't be called directly from addNode as that messes up the beta expansion).
    var branches = this.tree.closedBranches.concat(this.tree.openBranches);
    for (var i=0; i<branches.length; i++) {
        if (branches[i] == this) continue;
        var merge = true;
        nodeLoop:
        for (var j=0; j<branches[i].nodes.length; j++) {
            for (var k=0; k<this.nodes.length; k++) {
                if (this.nodes[k].formula.equals(branches[i].nodes[j].formula)) continue nodeLoop;
            }
            // debug("can't merge "+this.nodes+" with "+branches[i].nodes+" because of "+branches[i].nodes[j]);
            merge = false;
            break;
        }
        if (merge) {
            debug(this.tree);
            debug("Merging: removing " + this.nodes + " from tree as it contains " + branches[i].nodes);
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
    return this.unexpanded + "-" + this.literals;
}


function Node(formula, developedFrom) {
    if (!formula) return;
    this.formula = formula;
    this.developedFrom = developedFrom || null;
    switch (formula[0]) {
        case tc.AND : this.type = tc.ALPHA; break;
        case tc.OR : this.type = tc.BETA; break;
        case tc.ALL : this.type = tc.GAMMA; break;
        case tc.SOME : this.type = tc.DELTA; break;
        default: this.type = tc.LITERAL; break;
    }
    this.id = Node.counter++;
}
Node.counter = 0;

Node.prototype.getSubNode = function(subIndex) {
    return new Node(this.formula[subIndex], this);
}

Node.prototype.toString = function() {
    return translator.fla2html(this.formula);
}


function ModelFinder(formula) {
    debug("Creating ModelFinder for " + formula);
    var rootNode = new Node(formula.normalize());
    this.model = {
        domain : [],
        interpretation : [],
        toString : function() {
            var str = "<table>";
            str += "<tr><td>Domain: </td><td align='left'>{ ";
            str += this.domain.join(", ");
            str += " }</td></tr>";
            for (var p in this.interpretation) {
                if (Array.prototype[p]) continue;
                var inter = this.interpretation[p];
                if (typeof inter == "boolean") var extension = inter;
                else if (!inter.isArray) var extension = inter;
                else {
                    var ext = getExtension(inter, this.domain);
                    var extension = "{ ";
                    if (translator.getType(p) == tc.CONSTANT) { // functor
                        for (var i=0; i<ext.length; i++) {
                            extension += "&lt;" + ext[i].join(", ") + "&gt;"
                            if (i < ext.length-1) extension += ", ";
                        }
                    }
                    else { // predicate
                        var els = [];
                        for (var i=0; i<ext.length; i++) {
                            if (ext[i][ext[i].length-1] === false) continue;
                            if (ext[i].length == 2) els.push(ext[i][0]);
                            else els.push("&lt;" + ext[i].splice(0, ext[i].length-1).join(", ") + "&gt;");
                        }
                        extension += els.join(", ");
                    }
                    extension += " }";
                }
                str += "<tr><td align='right' class='formula'>" + translator.term2html(p) + ": </td><td align='left'>" + extension + "</td></tr>";
            }
            str += "</table>";
            return str;
            
            function getExtension(inter, domain) {
                var res = [];
                for (var i=0; i<domain.length; i++) {
                    if (inter[domain[i]] == undefined) continue;
                    if (inter[domain[i]].isArray) {
                        var subExt = getExtension(inter[domain[i]], domain);
                        for (var j=0; j<subExt.length; j++) res.push([domain[i]].concat(subExt[j]));
                    }
                    else res.push([domain[i], inter[domain[i]]]);
                }
                return res;
            }
        }
    }
    var model = this.model;
    var consts = rootNode.formula.getConstants(true); // a constant is { constant : x, arity : n }
    var preds = rootNode.formula.getPredicates(true); // a predicate is { pred : x, arity : n }
    
    this.isModel = function() {
        return interpret(rootNode);
    }
    
    function interpret(node) {
        // this could be sped up a lot xxx
        // debug("interpret "+node);
        switch (node.type) {
            case tc.ALPHA : return interpret(node.getSubNode(1)) && interpret(node.getSubNode(2));
            case tc.BETA : return interpret(node.getSubNode(1)) || interpret(node.getSubNode(2));
            case tc.GAMMA : {
                var matrixNode = new Node(node.formula[2]);
                for (var i=0; i<model.domain.length; i++) {
                    model.interpretation[node.formula[1]] = model.domain[i];
                    var res = interpret(matrixNode)
                    delete model.interpretation[node.formula[1]];
                    if (!res) return false;
                }
                return true;
            }
            case tc.DELTA : {
                var matrixNode = new Node(node.formula[2]);
                for (var i=0; i<model.domain.length; i++) {
                    model.interpretation[node.formula[1]] = model.domain[i];
                    var res = interpret(matrixNode)
                    delete model.interpretation[node.formula[1]];
                    if (res) return true;
                }
                return false;
            }
            case tc.LITERAL : {
                var fla = (node.formula[0] == tc.NOT) ? node.formula[1] : node.formula;
                var inter = model.interpretation[fla[0]];
                for (var i=0; i<fla[1].length; i++) {
                    var tval = fla[1][i].isArray ? interpret(fla[1][i]) : model.interpretation[fla[1][i]];
                    inter = inter[tval];
                    if (inter === undefined) break;
                }
                return (node.formula[0] == tc.NOT) ? !inter : !!inter;
            }
            default : { // 'node' is a term array [a,b,c] representing a(b,c)
                var inter = model.interpretation[node[0]];
                for (var i=1; i<node.length; i++) {
                    var tval = node[i].isArray ? interpret(node[i]) : model.interpretation[node[i]];
                    inter = inter[tval];
                }
                return inter;
            }
        }
    }
    
    this.search = function(numModels) {
        for (var i=0; i<numModels; i++) {
            if (!nextInterpretation()) initDomain(model.domain.length+1);
            debug("trying model "+model);
            if (this.isModel()) {
                debug("yep, model satisfies " + rootNode.formula);
                return model;
            }
            debug("no, model doesn't satisfy " + rootNode.formula);
        }
        return null;
    }
    
    function nextInterpretation() {
        var arr = arguments[0] || model.interpretation;
        for (var i=0; i<arr.length; i++) {
            if (arr[i] === undefined) continue;
            if (arr[i].isArray) {
                if (nextInterpretation(arr[i])) return true;
                continue;
            }
            if (typeof arr[i] == "boolean") {
                if ((arr[i] = !arr[i])) return true;
                continue;
            } 
            if (++arr[i] < model.domain.length) return true;
            arr[i] = 0;
        }
        return false;
    }
    
    function initDomain(numIndividuals) {
        // defines a (first) interpretation of the predicates and constants on the domain of
        // numbers 0,1,2,...(numIndividuals-1), so that for 0-ary p,a, 1-ary F,f, n-ary R,g:
        //    interpretation[a] = 0
        //    interpretation[p] = false
        //    interpretation[F][i] = false            for all i in the domain
        //    interpretation[R][i_1]...[i_n] = false  for all i_1,...,i_n in the domain
        //    interpretation[f][i] = 0                for all i in the domain
        //    interpretation[g][i_1]...[i_n] = 0      for all i_1,...,i_n in the domain
        debug("modelFinder initDomain("+numIndividuals+")");
        model.domain = [];
        for (var i=0; i<numIndividuals; i++) model.domain.push(i); // domain is integers 0,1,...
        for (var i=0; i<preds.length; i++) {
            if (preds[i].arity == 0) {
                model.interpretation[preds[i].predicate] = false;
                continue;
            }
            var arrs = [model.interpretation[preds[i].predicate] = []];
            for (var n=1; n<preds[i].arity; n++) {
                var narrs = [];
                for (var j=0; j<arrs.length; j++) {
                    for (var d=0; d<numIndividuals; d++) narrs.push(arrs[j][d] = []);
                }
                arrs = narrs;
            }
            for (var j=0; j<arrs.length; j++) {
                for (var d=0; d<numIndividuals; d++) arrs[j][d] = false;
            }
        }
        for (var i=0; i<consts.length; i++) {
            if (consts[i].arity == 0) {
                model.interpretation[consts[i].constant] = 0;
                continue;
            }
            var arrs = [model.interpretation[consts[i].constant] = []];
            for (var n=2; n<consts[i].arity; n++) {
                var narrs = [];
                for (var j=0; j<arrs.length; j++) {
                    for (var d=0; d<numIndividuals; d++) narrs.push(arrs[j][d] = []);
                }
                arrs = narrs;
            }
            for (var j=0; j<arrs.length; j++) {
                for (var d=0; d<numIndividuals; d++) arrs[j][d] = 0;
            }
        }
    }
    
}

