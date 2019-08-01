//
// A SenTree is a tableau in the familiar sentence format (without
// free variables). The SenTree constructor takes a Tree object (a
// free-variable tableau) as argument.
//
// Unlike Tree objects, SenTrees have their nodes really stored in
// tree form:
//
//    root
//
// is the root node,
//
//    node.children
//
// is an array of a nodes children,
//
//    node.parent
//
// the node's parent. Other than that, the nodes are the same Node
// objects as on Tree Branches.
//
// The only interesting method of SenTree, besides its constructor, is
//
//    getCounterModel
//
// which creates a ModelFinder and reads off a counterModel from an
// open tableau.
//

function SenTree(fvTree) {
    this.nodes = [];
    this.isClosed = (fvTree.openBranches.length == 0);
    this.initFormulas = fvTree.prover.initFormulas;
    this.initFormulasNonModal = fvTree.prover.initFormulasNonModal;
    this.initFormulasNormalized = fvTree.prover.initFormulasNormalized;
    this.parser = this.initFormulas[0].parser;
    this.fvTree = fvTree;
    this.freeVariables = [];
    //this.constants = []; xxx del
    
    this.collectVariables();
    this.markEndNodesClosed();
    this.transferNodes();
    log(this);
    this.replaceFreeVariables();
    log(this);
    this.replaceSkolemTerms();
    log(this);
    this.removeUnusedNodes();
    log(this);
}

SenTree.prototype.collectVariables = function() {
    // collect free variables from the fvtree and put them into arrays
    // if (this.parser.isModal) {
    //     // free world variables all originate from expanding □/gamma
    //     // formulas ∀v(wRv→..) into (wRξ7→..); so we can find the world
    //     // variables by looking through wRξ7 type nodes.
    //     for (var i=0; i<this.nodes.length; i++) {
    //         var fla = this.nodes[i].formula;
    //         if (fla.predicate == this.parser.R &&
    //             fla.terms[1][0] == 'ξ' &&
    //             !this.freeWorldVariables.includes(fla.terms[1])) {
    //             this.freeWorldVariables.push(fla.terms[1]);
    //         }
    //     }
    // }
    
    var branches = this.fvTree.closedBranches.concat(this.fvTree.openBranches);
    for (var b=0; b<branches.length; b++) {
        var branch = branches[b];
        for (var i=0; i<branch.freeVariables.length; i++) {
            if (!this.freeVariables.includes(branch.freeVariables[i])) {
                this.freeVariables.push(branch.freeVariables[i]);
            }
        }
        // for (var i=0; i<branch.constants.length; i++) {
        //     if (!this.constants.includes(branch.constants[i])) {
        //         this.constants.push(branch.constants[i]);
        //     }
        // }
    }
}

SenTree.prototype.markEndNodesClosed = function() {
    for (var i=0; i<this.fvTree.closedBranches.length; i++) {
        var branch = this.fvTree.closedBranches[i]; 
        branch.nodes[branch.nodes.length-1].closedEnd = true;
    }
}


SenTree.prototype.transferNodes = function() {
    // translates the free-variable tableau into sentence tableau and translate
    // all formulas back from negation normal form.
    //
    // If A is a formula and A' its NNF then expanding A' always results in
    // nodes that also correctly expand A, when denormalized. Remember that
    // normalization drives in all negations and converts (bi)conditionals into
    // ~,v,&. For example, |~(BvC)| = |~B|&|~C|. Expanding the NNF leads to |~B|
    // and |~C|. Expanding the original formula ~(BvC) would instead lead to ~B
    // and ~C. So we can construct the senTree by going through each node X on
    // the fvTree, identity the node Y corresponding to X's origin (the node
    // from which X is expanded), expand Y by the senTree rules and mark the
    // result as corresponding to X whenever the result's NNF is X.
    //
    // Exceptions: (1) NNFs remove double negations; so DNE steps have to be
    // reinserted. (2) Biconditionals are replaced by disjunctions of
    // conjunctions in NNF, but the classical senTree rules expand them in one
    // go, so we have to remove the conjunctive formulas.

    log("initializing sentence tableau nodes");

    this.addInitNodes();
    
    // go through all nodes on all branches, denormalize formulas and restore
    // standard order of subformula expansion:
    var branches = this.fvTree.closedBranches.concat(this.fvTree.openBranches);
    for (var b=0; b<branches.length; b++) {
        var par; // here we store the parent node of the present node
        for (var n=0; n<branches[b].nodes.length; n++) {
            var node = branches[b].nodes[n];
            if (node.isSenNode) {
                // node already on sentree
                par = node.swappedWith || node;
                continue;
            }
            // <node> not yet collected, <par> is its (already collected) parent
            log(this);
            par = this.transferNode(node, par);
        }
    }
}

SenTree.prototype.transferNode = function(node, par) {
    // transfer <node> from fvTree and append it to <par> node on sentree;
    // return next par node.
    //
    // Example: <node> is expanded from ¬(A→(B→C)). In the fvTree, the source
    // node has been normalized to A∧(B∧¬C), and <node> is (B∧¬C). We need to
    // figure out that this is the second node coming from the source node, so
    // that expansions are in the right order (and later references to
    // expansions of <node> reference the correct node). We also need to epand
    // the node as ¬(B→C) rather than (B∧¬C), to undo the normalization.
    //
    // So here's what we do: we first re-apply the rule (e.g. alpha) by which
    // <node> was created to the unnormalized source formula. We then compare
    // these which of these results, if normalized, equals <node>.formula and
    // overwrite <node>.formula with the unnormalized matching formula.
    
    var nodeFormula = node.formula;

    // first insert double negation elimination steps:
    for (var i=0; i<node.fromNodes.length; i++) {
        if (node.fromNodes[i].formula.type == 'doublenegation') {
            this.expandDoubleNegation(node.fromNodes[i]);
            log('setting fromNode '+i+' of '+node+' to '+node.fromNodes[i].dneTo);
            node.fromNodes[i] = node.fromNodes[i].dneTo; // this also changes
                                                         // fromNodes of other
                                                         // nodes with
                                                         // same fromNodes!
        }
    }
    if (par.dneTo) par = par.dneTo;
        
    switch (node.fromRule) {
    case Prover.alpha : {
        var from = node.fromNodes[0];
        log("transferring "+node+" (alpha from "+from+")");
        var f1 = from.formula.alpha(1);
        var f2 = from.formula.alpha(2);
        log("alpha1 "+f1+" alpha2 "+f2);

        // if <from> is the result of a biconditional application, reset
        // fromNodes[0] to the biconditional (A<->B is expanded to A&B | ~A&~B):
        if (from.biconditionalExpansion) {
            // all nodes added in an expansion must have identical .fromNodes!
            node.fromNodes = from.fromNodes;
        }
        
        // We know that <node> comes from the alpha formula <from>; <f1> and
        // <f2> are the two formulas that could legally be derived from <from>.
        // We need to find out which of these corresponds to <node>. [I used to
        // do node.formula = (node.formula.equals(f1.normalize())) ? f1 : f2;
        // but this breaks if f2.normalize() == f1.normalize() and f2 != f1,
        // e.g. in ¬((A∧¬A)∧¬(¬A∨¬¬A).]
        
        if (!nodeFormula.equals(f1.normalize())) node.formula = f2;
        else if (!nodeFormula.equals(f2.normalize())) node.formula = f1;
        else {
            // node formula matches both alpha1 and alpha2: if previous node
            // also originates from <from> by the alpha rule, this one must be
            // the second.
            node.formula = (par.fromNodes[0] && par.fromNodes[0] == from) ? f2 : f1;
        }
        this.appendChild(par, node);
        // restore correct order of alpha expansions:
        if (par.fromNodes[0] && par.fromNodes[0] == from && node.formula == f1) {
            this.reverse(par, node);
            return par;
        }
        else return node;
        
        // <>A = (Ev)(wRv & Av) is expanded to wRv & Av. 
        
    }
        
    case Prover.beta: {
        var from = node.fromNodes[0];
        log("transferring "+node+" (beta from "+from+")");
        var f1 = from.formula.beta(1);
        var f2 = from.formula.beta(2);
        log("beta1 "+f1+" beta2 "+f2);
        if (!nodeFormula.equals(f1.normalize())) node.formula = f2;
        else if (!nodeFormula.equals(f2.normalize())) node.formula = f1;
        else {
            // node formula matches both beta1 and beta2: if parent node already
            // has a child, this one is the second:
            node.formula = (par.children && par.children.length) ? f2 : f1;
        }
        // if <node> is the result of a biconditional application, mark it
        // unused for removal (A<->B is expanded to A&B | ~A&~B):
        if (from.formula.operator == '↔' ||
            (from.formula.operator == '¬' && from.formula.sub.operator == '↔')) {
            node.biconditionalExpansion = true;
            node.used = false;
            // xxx TODO what if we have a tree with nodes ¬(A&B) and (A<->B)?! This
            // will be closed with the hidden biconditional expansion node!
        }
        this.appendChild(par, node);
        if (par.children.length == 2 && node.formula == f1) {
            log('swapping children because node.formula == beta1');
            par.children.reverse();
        }
        return node;
    }
        
    case Prover.gamma: case Prover.delta: {
        // <node> is the result of expanding a (possibly negated)
        // quantified formula.
        var from = node.fromNodes[0];
        log("transferring "+node+" (gamma/delta from "+from+")");
        var newFla = from.formula.sub ? from.formula.sub.matrix.negate() : from.formula.matrix;
        var boundVar = from.formula.sub ? from.formula.sub.variable : from.formula.variable;
        log(boundVar + ' is instantiated (in '+newFla+') by '+node.instanceTerm);
        node.formula = newFla.substitute(boundVar, node.instanceTerm);
        this.appendChild(par, node);
        return node;
    }

    case Prover.modalGamma: {
        // <node> is the result of expanding a □ or ¬◇ formula.
        var from = node.fromNodes[0];
        log("transferring "+node+" (modalGamma from "+from+")");
        if (from.formula.sub) { // from = ¬◇A = ¬∃v(wRv ∧ Av)
            var newFla = from.formula.sub.matrix.sub2.negate();
            var boundVar = from.formula.sub.variable;
        }
        else { // from = □A = ∀v(wRv → Av)
            var newFla = from.formula.matrix.sub2;
            var boundVar = from.formula.variable;
        }
        log(boundVar + ' is instantiated (in '+newFla+') by '+node.instanceTerm);
        node.formula = newFla.substitute(boundVar, node.instanceTerm);
        this.appendChild(par, node);
        return node;
    }

    default: {
        this.appendChild(par, node);
        return node;
    }
    }
}

SenTree.prototype.addInitNodes = function() {
    // add initNodes to tree with their original formula (de-normalized) xxx add
    // world label to modal fla?
    var branch = this.fvTree.closedBranches.length > 0 ?
        this.fvTree.closedBranches[0] : this.fvTree.openBranches[0];
    
    for (var i=0; i<this.initFormulasNonModal.length; i++) {
        log('adding init node '+branch.nodes[i]);
        var node = this.makeNode(branch.nodes[i]);
        node.formula = this.initFormulasNonModal[i]; // yes, we overwrite the node's original
                                             // (normalized) formula -- don't need
                                             // it anymore.
        if (i==0) this.nodes.push(node);
        else this.appendChild(nodes[i-1], node);
    }
}

SenTree.prototype.expandDoubleNegation = function(node) {
    // expand doublenegation node <node> on current tree
    log("expanding double negation "+node);
    var newNode = new Node(node.formula.sub.sub, null, [node]);
    this.makeNode(newNode);
    node.dneTo = newNode;
    // if <node> is first result of alpha expansion, dne node must be inserted
    // after second result:
    var dnePar = node;
    if (node.children[0] && node.children[0].fromNodes == node.fromNodes) {
        dnePar = node.children[0];
    }
    newNode.parent = dnePar;
    newNode.children = dnePar.children;
    dnePar.children = [newNode];
    for (var i=0; i<newNode.children.length; i++) {
        newNode.children[i].parent = newNode;
    }
    newNode.used = node.used;
    this.nodes.push(newNode);
} 

SenTree.prototype.replaceFreeVariables = function() {
    log("replacing free variables by new constants");
    for (var i=0; i<this.freeVariables.length; i++) {
        this.substitute(this.freeVariables[i], this.parser.getNewConstant());
    }
}

SenTree.prototype.removeUnusedNodes = function() {
    log("removing unused nodes");
    if (!this.isClosed) return;
    // first, mark all nodes that were added along with used nodes as used:
    for (var i=0; i<this.nodes.length; i++) {
        var node = this.nodes[i];
        if (node.used) {
            var expansion = this.getExpansion(node);
            for (var j=0; j<expansion.length; j++) {
                if (!expansion[j].biconditionalExpansion) {
                    expansion[j].used = true;
                }
            }
        }
    }
    // now remove all unused nodes:
    for (var i=0; i<this.nodes.length; i++) {
        if (!this.nodes[i].used) {
            var ok = this.remove(this.nodes[i]);
            if (ok) i--; // reducing i because remove() removed it from the array
        }
    }
}


SenTree.prototype.replaceSkolemTerms = function() {
    log("replacing skolem terms");
    // skolem terms all look like 'φ1', 'φ1(𝛏1,𝛏2..)'; after unification
    // they can also be nested: '𝛗1(𝛏1,𝛗2(𝛏1)..)'. Note that a skolem term
    // can occur inside an ordinary function term. xxx Need to check if this
    // should be accounted for; substitution is shallow...
    var translations = {};
    for (var n=0; n<this.nodes.length; n++) {
        var skterms = getSkolemTerms(this.nodes[n].formula);
        var indivTerms = skterms[0], worldTerms = skterms[1];
        for (var c=0; c<indivTerms.length; c++) {
            var termstr = indivTerms[c].toString();
            if (!translations[termstr]) {
                log(termstr + " is skolem term");
                translations[termstr] = this.parser.getNewConstant();
                // this.constants.push(translations[termstr]); // xxx do I need this.constants?
            }
            this.nodes[n].formula = this.nodes[n].formula.substitute(
                indivTerms[c], translations[termstr], true
            );
        }
        for (var c=0; c<worldTerms.length; c++) {
            var termstr = worldTerms[c].toString();
            if (!translations[termstr]) {
                log(termstr + " is worldly skolem term");
                translations[termstr] = this.parser.getNewWorldName(true);
            }
            this.nodes[n].formula = this.nodes[n].formula.substitute(
                worldTerms[c], translations[termstr], true
            );
        }
    }
    function getSkolemTerms(formula) {
        if (formula.string.indexOf('φ') == -1) return [[],[]];
        var indivTerms = [], worldTerms = [];
        var flas = [formula];
        var fla;
        while ((fla = flas.shift())) {
            if (fla.sub) {
                flas.unshift(fla.sub);
            }
            else if (fla.sub1) {
                flas.unshift(fla.sub1);
                flas.unshift(fla.sub2);
            }
            else if (fla.matrix) {
                flas.unshift(fla.matrix);
            }
            else {
                for (var i=0; i<fla.terms.length; i++) {
                    var skterm = null;
                    // xxx todo tidy up the next few lines
                    if (fla.terms[i].isArray) {
                        if (fla.terms[i][0][0] == 'φ') skterm = fla.terms[i];
                    }
                    else if (fla.terms[i][0] == 'φ') skterm = fla.terms[i];
                    if (skterm) {
                        if (formula.parser.isModal && i == fla.terms.length-1) {
                            // final term denotes a world
                            worldTerms.push(skterm);
                        }
                        else indivTerms.push(skterm);
                    }
                }
            }
        }
        return [indivTerms, worldTerms];
    }
}

SenTree.prototype.modalize = function() {
    // undo standard translation for formulas on the tree, and hide some nodes
    // to make tree look like a familiar modal tree.
    //
    // Example: ◇(p→q) is translated into ∃v(wRv ∧ (pv → qv)), and expanded into
    // (wRu ∧ (pu → qu)). This is further expanded to wRu and (pu → qu). We want
    // to hide the direct result of first expansion and translate (pu → qu) back
    // into (p → q) with world label u.
    //
    // Example: □p is translated into ∀v(wRv → pv), expanded by modalGamma to pu.

    var removeNodes = [];
    for (var i=0; i<this.nodes.length; i++) {
        
        var node = this.nodes[i];
        var formula = node.formula;
        log('modalising '+formula);

        if (formula.predicate == this.parser.R) {
            // wRv nodes
            formula.string = formula.terms[0] + formula.predicate + formula.terms[1];
        }
        
        // catch modal expansions: ◇A => (Rxy∧A), ¬□A => ¬(Rxy→A), □A =>
        // (Rxy→A), ¬◇A => ¬(Rxy∧A). xxx update comment
        if ((formula.sub1 && formula.sub1.predicate == this.parser.R) ||
            (formula.sub && formula.sub.sub1 && formula.sub.sub1.predicate == this.parser.R)) {
            log('marking modal expansion '+formula.string+' for removal');
            removeNodes.push(node);
        }
        
        if (removeNodes.includes(node.fromNodes[0])) {
            // remove leaf nodes expanded from (Rxy→A) or ¬(Rxy∧A):
            // if (formula.sub && formula.sub.predicate == this.parser.R) {
            //     log('marking leaf node '+formula+' for removal');
            //     removeNodes.push(node);
            //     continue;
            // }
            // adjust fromNodes of surviving nodes descending from modal
            // expansions:
            var modalExpansion = node.fromNodes[0];
            if (modalExpansion.fromNodes[0].formula.type == 'diamondy') {
                // ◇A => Rxy,A come from ◇A; ¬□A => Rxy,¬A come from ¬□A
                node.fromNodes = modalExpansion.fromNodes;
                // xxx could node.fromNodes have more than 1 member here?
            }
            else { // 'boxy' origin
                // □A => [removed ¬Rxy],A come from □A AND Rxy node; ¬◇A => [removed
                // ¬Rxy],A come from ¬◇A AND Rxy node
                // node.fromNodes = [modalExpansion.fromNodes[0]];
                // // find Rxy node: first, get 'Rxy' string from removed sibling:
                // var sibf = node.parent.children[0].formula.sub;
                // var rxy = sibf.terms[0] + sibf.predicate + sibf.terms[1];
                // log('rxy = '+rxy);
                // for (var anc=node.parent; anc; anc=anc.parent) {
                //     if (anc.formula.string == rxy) {
                //         node.fromNodes.push(anc);
                //         log('match: '+anc);
                //         break;
                //     }
                // }
            }
            log('adjusting fromNodes of '+formula+' to '+node.fromNodes);
        }
        
        node.formula = formula.translateToModal();
        // log(formula+' => '+node.formula);
        // log('w: '+node.formula.world);
    }

    for (var i=0; i<removeNodes.length; i++) {
        this.remove(removeNodes[i]);
    }
    
    log(this);
}


SenTree.prototype.makeNode = function(node) {
    node.parent = null;
    node.children = [];
    node.isSenNode = true;
    return node;
}

SenTree.prototype.appendChild = function(oldNode, newNode) {
   log("appending "+newNode+" to "+ oldNode); 
   if (!newNode.isSenNode) {
       newNode = this.makeNode(newNode);
   }
   newNode.parent = oldNode;
   oldNode.children.push(newNode);
   if (oldNode.closedEnd) {
      oldNode.closedEnd = false;
      newNode.closedEnd = true;
   }
   this.nodes.push(newNode);
   return newNode;
}

SenTree.prototype.remove = function(node) {
    if (node.isRemoved) return;
    log("removing " + node + " (parent: " + node.parent + ", children: " + node.children + ")");
    if (node.parent.children.length == 1) {
        node.parent.children = node.children;
        if (node.children[0]) {
            node.children[0].parent = node.parent;
            node.children[0].instanceTerm = node.instanceTerm;
        }
        if (node.children[1]) {
            node.children[1].parent = node.parent;
            node.children[1].instanceTerm = node.instanceTerm;
        }
    }
    else {
        if (node.children.length > 1) {
            log("can't remove a node with two children that itself has a sibling");
            return false;
        }
        var i = (node == node.parent.children[0]) ? 0 : 1;
        if (node.children[0]) {
            node.parent.children[i] = node.children[0];
            node.children[0].parent = node.parent;
            node.children[0].instanceTerm = node.instanceTerm;
        }
        else node.parent.children.remove(node);
    }
    this.nodes.remove(node);
    node.isRemoved = true;
    return true;
}

SenTree.prototype.toString = function() {
   // for debugging only
   return "<table><tr><td align='center' style='font-family:monospace'>"+getTree(this.nodes[0])+"</td</tr></table>";
   function getTree(node) {
      var recursionDepth = arguments[1] || 0;
      if (++recursionDepth > 40) return "<b>...<br>[max recursion]</b>";
      var res = (node.used ? '.' : '') + node + (node.closedEnd ? "<br>x<br>" : "<br>");
      if (node.children[1]) res += "<table><tr><td align='center' valign='top' style='font-family:monospace; border-top:1px solid #999; padding:3px; border-right:1px solid #999'>" + getTree(node.children[0], recursionDepth) + "</td>\n<td align='center' valign='top' style='padding:3px; border-top:1px solid #999; font-family:monospace'>" + getTree(node.children[1], recursionDepth) + "</td>\n</tr></table>";
      else if (node.children[0]) res += getTree(node.children[0], recursionDepth);
      return res;
   }
}

SenTree.prototype.substitute = function(oldTerm, newTerm) {
    for (var i=0; i<this.nodes.length; i++) {
        log("substituting "+oldTerm+" by "+newTerm+" in "+this.nodes[i].formula);
        this.nodes[i].formula = this.nodes[i].formula.substitute(oldTerm, newTerm);
    }
}

SenTree.prototype.reverse = function(node1, node2) {
   // swaps the position of two immediate successor nodes
   node2.parent = node1.parent;
   node1.parent = node2;
   if (node2.parent.children[0] == node1) node2.parent.children[0] = node2;
   else node2.parent.children[1] = node2;
   node1.children = node2.children;
   node2.children = [node1];
   if (node1.children[0]) node1.children[0].parent = node1;
   if (node1.children[1]) node1.children[1].parent = node1;
   if (node2.closedEnd) {
      node2.closedEnd = false;
      node1.closedEnd = true;
   }
   node2.swappedWith = node1;
   node1.swappedWith = node2;
}

SenTree.prototype.getExpansion = function(node) {
    // returns all nodes that were added to the tree in the same expansion step
    // as the given node.

    // Here we exploit the fact that when a rule creates several nodes, these
    // have the strictly same array as fromNodes.

    if (node.fromNodes.length == 0) return [node];

    var res = [node];

    // get ancestors from same rule application:
    var par = node.parent;
    while (par && par.fromNodes == node.fromNodes) {
        res.unshift(par);
        par = par.parent;
    }
    
    // get descendants from same rule application:
    var ch = node.children[0];
    while (ch && ch.fromNodes == node.fromNodes) {
        res.push(ch);
        ch = ch.children[0];
    }
    
    // get siblings from same rule application:
    if (par) {
        for (var i=0; i<par.children.length; i++) {
            var sib = par.children[i];
            while (sib && sib.fromNodes == node.fromNodes) {
                if (!res.includes(sib)) res.push(sib);
                sib = sib.children[0];
            }
        }
    }
    
    return res;
}

SenTree.prototype.getCounterModel = function() {
    // Read off a (canonical) countermodel from an open branch.
    // First, find an open branch:
    var endNode = null;
    for (var i=0; i<this.nodes.length; i++) {
        if (this.nodes[i].children.length || this.nodes[i].closedEnd) continue;
        endNode = this.nodes[i];
        break;
    }
    if (!endNode) return null;
    log("creating counterModel from endNode " + endNode);
    var modelFinder = new ModelFinder(this.initFormulasNormalized);
    var model = modelFinder.model;
    model.initInterpretation(1);
   
    // set up the domain and map every term to a number in the domain; remember
    // that f(a) may denote an individual that is not denoted by any individual
    // constant.
    var numIndividuals = 0;
    var terms2individuals = {};
    var node = endNode;
    do {
        var fla = node.formula;
        while (fla.operator == '¬') fla = fla.sub; // note that there may be unexpanded DN atoms on the branch
        if (!fla.predicate) continue; 
        var terms = fla.terms.copy();
        for (var t=0; t<terms.length; t++) {
            if (terms2individuals[terms[t].toString()]) continue;
            log("adding element for "+terms[t]);
            model.domain.push(numIndividuals);
            terms2individuals[terms[t].toString()] = numIndividuals;
            if (terms[t].isArray) {
                for (var i=1; i<terms[t].length; i++) terms.push(terms[t][i]);
            }
            else model.values[terms[t]] = numIndividuals; // set up interpretation for constants
            numIndividuals++;
        }
    } while ((node = node.parent));
    if (numIndividuals == 0) {
        model.domain = [0];
        numIndividuals = 1;
    }
   
    // Now interpret function and predicate symbols.
    // For function terms, a canonical model should assign to f^n a function F such that 
    // for all (t1...tn) for which f(t1...tn) occurs on the branch, F(T1...Tn) = "f(t1...tn)",
    // where Ti is the intepretation of ti (i.e. the string "ti"). For all other arguments
    // not occuring on the branch as arguments of f, the value of F is arbitrary. 
    // (Note that in a complete canonical tableau, GAMMA formulas are expanded for all terms
    // on the branch. So if Ax~Gf(x)&Ga is on the branch, then so are ~Gf(a), ~Gf(f(a)), etc.
    // All open branches on a complete canonical tableaux containing functional terms are thus
    // infinite. The current tree will never be infinite, so it's always by luck if it finds a 
    // model in this case.)
    node = endNode;
    do {
        var fla = node.formula;
        var tv = true;
        while (fla.operator == '¬') {
            fla = fla.sub;
            tv = !tv;
        }
        if (!fla.predicate) continue;
        log("interpreting " + node);
        if (fla.terms.length == 0) { // propositional constant
            model.values[fla.predicate] = tv;
            continue;
        }
        // interpret function symbols:
        var subTerms = fla.terms.copy();
        for (var t=0; t<subTerms.length; t++) {
            var term = subTerms[t];
            if (!term.isArray) continue;
            var functor = term[0], args = term.slice(1);
            if (!model.values[functor]) {
                // init functor interpretation; recall that model.values['f'] is
                // the list of function values, e.g. [0,1,0,0] corresponding to
                // the list of possible function arguments, e.g. [<0,0>, <0,1>,
                // <1,0>, <1,1>]. This second list is stored in
                // model.argLists[arity].
                var arity = args.length;
                if (!model.argLists[arity]) {
                    model.argLists[arity] = Model.initArguments(arity, numIndividuals);
                }
                model.values[functor] = Array.getArrayOfZeroes(model.argLists[arity].length);
            }
            // now make sure the value assigned to 'f' for the value of '(ab)'
            // is terms2individuals['f(ab)'];
            var argValues = [];
            for (var i=0; i<args.length; i++) {
                argValues.push(terms2individuals[args[i].toString()]);
            }
            var argsIndex = model.argLists[arity].indexOf(argValues.toString());
            model.values[functor][argsIndex] = terms2individuals[term.toString()]; 
        }
        // interpret predicate:
        if (!model.values[fla.predicate]) {
            var arity = fla.terms.length; // always >0 because we've dealt with the other case before
            if (!model.argLists[arity]) {
                model.argLists[arity] = Model.initArguments(arity, numIndividuals);
            }
            model.values[fla.predicate] = Array.getArrayOfZeroes(model.argLists[arity].length);
        }
        // make sure the value assigned to 'F' for the value of '(ab)' is tv:
        var argValues = [];
        for (var i=0; i<fla.terms.length; i++) {
            argValues.push(terms2individuals[fla.terms[i].toString()]);
        }
        var argsIndex = model.argLists[arity].indexOf(argValues.toString());
        model.values[fla.predicate][argsIndex] = tv;
        log(model);
    } while ((node = node.parent));
    log("model: " + model);
    if (model.satisfiesInitFormulas()) return model;
    return null;
}

