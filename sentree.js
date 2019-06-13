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

function SenTree(fvTree, initFormulas) {
    this.nodes = [];
    this.isClosed = (fvTree.openBranches.length == 0);
    this.initFormulas = initFormulas;
    tree = this;
    var branches = fvTree.closedBranches.concat(fvTree.openBranches);
    var freeVariables = [];
    var constants = [];
    
    collectVariablesAndConstants();

    log("initializing sentence tableau");
    initNodes();
    log(this);
   
    log("replaceFreeVariablesByNewConsts");
    for (var i=0; i<freeVariables.length; i++) {
        var newConst = (constants.length != 0) ? constants[constants.length-1] + 3 : 2;
        constants.push(newConst);
        this.substitute(freeVariables[i], newConst);
    }
    log(this);
   
    log("replaceSkolemTerms()");
    replaceSkolemTerms();
    log(this);
    
    log("removeUnusedNodes()");
    removeUnusedNodes();
    log(this);

    function collectVariablesAndConstants() {
        // collect free variables and constants from fvtree and put
        // them into variables and constants arrays
        for (var b=0; b<branches.length; b++) {
            // collect free variables and constants:
            for (var i=0; i<branches[b].freeVariables.length; i++) {
                if (!freeVariables.includes(branches[b].freeVariables[i])) {
                    freeVariables.push(branches[b].freeVariables[i]);
                }
            }
            for (var i=0; i<branches[b].constants.length; i++) {
                if (!constants.includes(branches[b].constants[i])) {
                    constants.push(branches[b].constants[i]);
               }
            }
        }
    }
    
    function initNodes() {
        // translates the free-variable tableau into sentence tableau and
        // translate all formulas back from negation normal form.
        //
        // If A is a formula and A' its NNF then expanding A' always results in
        // nodes that also correctly expand A, when denormalized. Remember that
        // normalization drives in all negations and converts (bi)conditionals
        // into ~,v,&. For example, |~(BvC)| = |~B|&|~C|. Expanding the NNF
        // leads to |~B| and |~C|. Expanding the original formula ~(BvC) would
        // instead lead to ~B and ~C. So we can construct the senTree by going
        // through each node X on the fvTree, identity the node Y corresponding
        // to X's origin (the node from which X is expanded), expand Y by the
        // senTree rules and mark the result as corresponding to X whenever the
        // result's NNF is X.
        //
        // Exceptions: (1) NNFs remove double negations; so DNE steps have to be
        // reinserted. (2) Biconditionals are replaced by disjunctions of
        // conjunctions in NNF, but the classical senTree rules expand them in
        // one go, so we have to remove the conjunctive formulas.

        for (var i=0; i<initFormulas.length; i++) {
            log('adding init node '+branches[0].nodes[i]);
            var node = tree.makeNode(branches[0].nodes[i]);
            node.formula = initFormulas[i]; // yes, we overwrite the node's
                                            // original (normalized) formula --
                                            // don't need it anymore
            if (i==0) tree.nodes.push(node);
            else treeappendChild(nodes[i-1], node);
        }
        
        // mark end nodes as closed:
        for (var i=0; i<fvTree.closedBranches.length; i++) {
            fvTree.closedBranches[i].nodes[fvTree.closedBranches[i].nodes.length-1].closedEnd = true;
        }
        
        // go through all nodes on all branches, denormalize formulas and
        // restore standard order of subformula expansion:
        for (var b=0; b<branches.length; b++) {
            var par; // here we store the parent node of the present node
            for (var n=0; n<branches[b].nodes.length; n++) {
                var node = branches[b].nodes[n];
                if (node.isSenNode) {
                    // node already on sentree
                    par = node.swappedWith || node;
                    continue;
                }
                // <node> not yet collected, <par> is its (already collected)
                // parent
            
                log(tree);
                var from = node.developedFrom;
                log("init "+node+" from "+from+", par "+par);
                
                switch (from.formula.type) {
                case 'alpha' : {
                    if (from.__removeMe) {
                        // if <from> is the result of a biconditional
                        // application, we remove it.
                        if (par == from) par = from.parent;
                        node.developedFrom = from.developedFrom;
                        tree.remove(from);
                    }
                   
                    var f1 = from.formula.alpha(1);
                    var f2 = from.formula.alpha(2);
                    log("alpha1 "+f1+" alpha2 "+f2);
                    
                    // We know that <node> comes from the alpha formula <from>;
                    // <f1> and <f2> are the two formulas that could legally be
                    // derived from <from>. We need to find out which of these
                    // corresponds to <node>. I used to do node.formula =
                    // (node.formula.equals(f1.normalize())) ? f1 : f2; but this
                    // breaks if f2.normalize() == f1.normalize() and f2 != f1,
                    // e.g. in \neg((A\land \negA)\land
                    // \neg(\negA\lor\neg\negA)). So we check for a sibling or
                    // parent node with the same <from>:
                    
                    if (!node.formula.equals(f1.normalize())) node.formula = f2;
                    else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                    else { // matches both
                        node.formula = (par.developedFrom == node.developedFrom) ? f2 : f1;
                    }
                    tree.appendChild(par, node);
                    
                    if (par.developedFrom == node.developedFrom && node.formula == f1) {
                        tree.reverse(par, node);
                    }
                    else par = node;
                    break;
                }
                case 'beta': {
                    var f1 = from.formula.beta(1);
                    var f2 = from.formula.beta(2);
                    if (!node.formula.equals(f1.normalize())) node.formula = f2;
                    else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                    else { // matches both
                        node.formula = (par.children && par.children.length) ? f2 : f1;
                    }
                    if (from.formula.operator == '↔' ||
                        (from.formula.operator == '¬' && from.formula.sub.operator == '↔')) {
                        node.__removeMe = true;
                    }
                    tree.appendChild(par, node);
                    
                    if (par.children.length == 2 && node.formula == f1) par.children.reverse();
                    par = node;
                    break;
                }
                case 'gamma': case 'delta': {
                    // <node> is the result of expanding a (possibly negated)
                    // quantified formula.
                    var newFla = from.formula.sub ? from.formula.sub.matrix.negate() : from.formula.matrix;
                    var boundVar = from.formula.sub ? from.formula.sub.variable : from.formula.variable;
                    log(boundVar + ' is instantiated (in '+newFla+') by '+node.instanceTerm);
                    node.formula = newFla.substitute(boundVar, node.instanceTerm);
                    tree.appendChild(par, node);
                    par = node;
                    break;
                }
                case 'doublenegation': {
                    // expand the DN node, then try again:
                    if (!from.dneTo) {
                        var newNode = new Node(from.formula.sub.sub, from);
                        tree.makeNode(newNode);
                        from.dneTo = newNode;
                        var dneToPar = (from.children[0] && from.children[0].developedFrom == from.developedFrom) ?
                            from.children[0] : from;
                        newNode.parent = dneToPar;
                        newNode.children = dneToPar.children;
                        for (var i=0; i<newNode.children.length; i++) {
                            newNode.children[i].parent = newNode;
                        }
                        dneToPar.children = [newNode];
                        newNode.used = from.used;
                        tree.nodes.push(newNode);
                        if (par == dneToPar) par = newNode; // adjust parent of current node
                    }
                    // double negation eliminated, now process node again:
                    node.developedFrom = from.dneTo;
                    par = (par == from) ? from.dneTo : par;
                    n -= 1;
                    break;
                }
                default: {
                    tree.appendChild(par, node);
                    par = node;
                }
                }
            }
        }
    }   

    function removeUnusedNodes() {
        // If the tree is closed, the used ancestors of all complementary pairs
        // are already marked .used, except DN elim formulas that didn't exist on
        // the original tree. We mark these .used and also the other node of a
        // used ALPHA or BETA expansion.
        if (!tree.isClosed) return;
        for (var i=0; i<tree.nodes.length; i++) {
            var node = tree.nodes[i];
            if (!node.used) {
                if (node.developedFrom && node.developedFrom.used &&
                    node.developedFrom.formula.operator == '¬' &&
                    node.developedFrom.formula.sub.operator == '¬') { // dne
                        node.used = true;
                }
                continue;
            }
            if (!node.developedFrom) continue;
            var expansion = tree.getExpansion(node);
            for (var j=0; j<expansion.length; j++) {
                expansion[j].used = true;
            }
        }
        for (var i=0; i<tree.nodes.length; i++) {
            if (!tree.nodes[i].used) {
                tree.remove(tree.nodes[i--]); // reducing i because remove() will remove it from the array
            }
        }
    }
    
    function replaceSkolemTerms() {
        // skolem terms all look like 'φ1', 'φ1(𝛏1,𝛏2..)'; after unification
        // they can also be nested: '𝛗1(𝛏1,𝛗2(𝛏1)..)'. Note that a skolem term
        // can occur inside an ordinary function term. xxx Need to check if this
        // should be accounted for; substitution is shallow...
        var translations = {};
        for (var n=0; n<tree.nodes.length; n++) {
            var skterms = getSkolemTerms(tree.nodes[n].formula);
            for (var c=0; c<skterms.length; c++) {
                var termstr = skterms[c].toString();
                log(termstr + " is skolem term");
                if (!translations[termstr]) {
                    translations[termstr] = newConstant();
                    constants.push(translations[termstr]);
                }
                tree.nodes[n].formula = tree.nodes[n].formula.substitute(
                    skterms[c], translations[termstr], true);
            }
        }
        function getSkolemTerms(formula) {
            var result = [];
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
                        if (fla.terms[i].isArray) {
                            if (fla.terms[i][0][0] == 'φ') result.push(fla.terms[i]);
                        }
                        if (fla.terms[i][0] == 'φ') result.push(fla.terms[i]);
                    }
                }
            }
            return result;
        }
        function newConstant() {
            var candidates = 'abcdefghijklmno';
            for (var i=0; i<candidates.length; i++) {
                if (!constants.includes(candidates[i])) return candidates[i];
            }
            for (var i=2; true; i++) {
                if (!constants.includes('a'+i)) return 'a'+i;
            }
        }
    }
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
        if (node.children.length > 1) throw "can't remove a node with two children that itself has a sibling";
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
    // as the given node
    log('expansion from '+node.formula.string);
    if (!node.developedFrom) return [node];
    var from = node.developedFrom;
    var fromOp = from.formula.operator;
    if (fromOp == '¬') {
        // negated conjunction is treated like disjunction, etc.
        fromOp = (from.formula.sub.operator == '∧') ? '∨'
            : (from.formula.sub.operator == '∨' || from.formula.sub.operator == '→') ? '∧' :
            from.formula.sub.operator;
    }
    switch (fromOp) {
    case '∧' : {
        if (node.children[0] && node.children[0].developedFrom == from) {
            return [node, node.children[0]];
        }
        if (node.parent.developedFrom == from) {
            return [node.parent, node];
        }
        return [node];
    }
    case '∨' : 
    case '→' : {
        return node.parent.children;
    }
    case '↔' : {
        var res = (node.children[0] && node.children[0].developedFrom == from) ? [node, node.children[0]]
            : (node.parent.developedFrom == from) ? [node.parent, node]
            : [node];
        if (!res[0].parent.children[1]) return res;
        var i = (res[0].parent.children[0] == res[0]) ? 1 : 0;
        res.push(res[0].parent.children[i]);
        if (res[0].parent.children[i].children[0] && res[0].parent.children[i].children[0].developedFrom == from) {
            res.push(res[0].parent.children[i].children[0]);
        }
        return res;
    }
    default : {
        return [node];
    }
    }
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
    var modelFinder = new ModelFinder(this.initFormulas);
    var model = modelFinder.model;
   
    // set up the domain and map every term onto itself:
    var node = endNode;
    do {
        var fla = node.formula;
        while (fla.operator == '¬') fla = fla.sub; // note that there may be unexpanded DN atoms on the branch
        if (!fla.predicate) continue; 
        var terms = fla.terms.copy();
        for (var t=0; t<terms.length; t++) {
            if (model.domain.includes(terms[t])) continue;
            log("adding "+terms[t]);
            model.domain.push(terms[t]);
            if (terms[t].isArray) {
                for (var i=1; i<terms[t].length; i++) terms.push(terms[t][i]);
            }
            else model.interpretation[terms[t]] = term;
        }
    } while ((node = node.parent));
    if (model.domain.length == 0) model.domain = [2];
    log("domain initialized: " + model);
   
    // interpret function and predicate symbols:
    // For functional terms, a canonical model should assign to f^n a function F such that 
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
            model.interpretation[fla.predicate] = tv;
            continue;
        }
        // interpret function symbols:
        var subTerms = fla.terms.copy();
        for (var t=0; t<subTerms.length; t++) {
            var term = subTerms[t];
            if (!term.isArray) continue;
            var functor = term[0], args = term.slice(1);
            if (!model.interpretation[functor]) {
                // init functor interpretation:
                var arrs = [model.interpretation[functor] = []];
                for (var n=2; n<args.length; n++) {
                    var narrs = [];
                    for (var j=0; j<arrs.length; j++) {
                        for (var d=0; d<model.domain.length; d++) {
                            narrs.push(arrs[j][model.domain[d]] = []);
                        }
                    }
                    arrs = narrs;
                }
                for (var j=0; j<arrs.length; j++) {
                    for (var d=0; d<model.domain.length; d++) {
                        arrs[j][model.domain[d]] = model.domain[0]; // default value is first individual
                    }
                }
                log("initialized functor interpretation: " + model);
            }
            // assign t[arg1]....[argn] = "t(arg1,...,argn)":
            var arrs = [model.interpretation[functor]];
            for (var i=1; i<term.length-1; i++) {
                var sTerm = translator.term2html(term[i]);
                arrs[i] = arrs[i-1][sTerm];
            }
            var lastSTerm = translator.term2html(term[term.length-1]);
            arrs[arrs.length-1][lastSTerm] = translator.term2html(term);
            for (var i=1; i<term.length; i++) subTerms.push(term[i]);
        }
        // interpret predicate:
        if (!model.interpretation[fla.predicate]) {
            model.interpretation[fla.predicate] = [];
        }
        var arrs = [model.interpretation[fla.predicate]];
        for (var i=0; i<fla.terms.length-1; i++) {
            var term = fla.terms[i];
            if (!arrs[i][term]) arrs[i][term] = [];
            arrs[i+1] = arrs[i][term];
        }
        var lastTerm = fla.terms[fla.terms.length-1];
        arrs[arrs.length-1][lastTerm] = tv;
        log(model);
    } while ((node = node.parent));
    log("model: " + model);
    if (modelFinder.isModel(model)) return model;
    return null;
}

