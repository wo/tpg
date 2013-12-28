//
// A SenTree is a tableau in the familiar sentence format (without free variables). 
// The SenTree constructor takes a Tree object (a free-variable tableau) as argument. 
//
// Unlike Tree objects, SenTrees have their nodes really stored in tree form: 
//    root
// is the root node, 
//    node.children
// is an array of a nodes children,
//    node.parent
// the node's parent. Other than that, the nodes are the same Node objects as on Tree
// Branches.
//
// The only interesting method of SenTree, besides its constructor, is
//    getCounterModel
// which creates a ModelFinder and reads off a counterModel from an open tableau.
//

function SenTree(fvTree) {
   this.nodes = [];
   this.rootNode = null;
   this.isClosed = (fvTree.openBranches.length == 0);
   var tree = this;
   var freeVariables = [];
   var constants = [];
   
   debug("initializing sentence tableau");
   initNodes();
   debug(this);
   
   debug("replaceFreeVariablesByNewConsts");
   for (var i=0; i<freeVariables.length; i++) {
      var newConst = (constants.length != 0) ? constants[constants.length-1] + 3 : 2;
      constants.push(newConst);
      this.substitute(freeVariables[i], newConst);
   }
   debug(this);
   
   debug("replaceSkolemTerms()");
   replaceSkolemTerms();
   debug(this);
   
   debug("removeUnusedNodes()");
   removeUnusedNodes();
   debug(this);
   
   function initNodes() {
      // translates the free-variable tableau into sentence form, also translates all formulas back from
      // negation normal form
      tree.rootNode = tree.nodes[0] = fvTree.rootNode;
      tree.rootNode.base = SenNode;
      tree.rootNode.base();
      tree.rootNode.formula = fvTree.rootFormula; // denormalized
      for (var i=0; i<fvTree.closedBranches.length; i++) {
         fvTree.closedBranches[i].nodes[fvTree.closedBranches[i].nodes.length-1].closedEnd = true;
      }
      var branches = fvTree.closedBranches.concat(fvTree.openBranches);
      for (var b=0; b<branches.length; b++) {
         for (var i=0; i<branches[b].freeVariables.length; i++) {
            if (!freeVariables.contains(branches[b].freeVariables[i])) freeVariables.push(branches[b].freeVariables[i]);
         }
         freeVariables.sort(function(a,b){ return a-b });
         for (var i=0; i<branches[b].constants.length; i++) {
            if (!constants.contains(branches[b].constants[i])) constants.push(branches[b].constants[i]);
         }
         constants.sort(function(a,b){ return a-b });
         var par;
         for (var n=0; n<branches[b].nodes.length; n++) {
            var node = branches[b].nodes[n];
            if (node.isSenNode) {
               par = node.swappedWith || node;
               continue;
            }
            // so it's a node not yet collected, par is its (already collected) parent
            
            // we denormalize the node formula, and restore the standard order of subformula expansion;
            debug(tree);
            var from = node.developedFrom;
            debug("init "+node+" (from "+from+", par "+par+")");
            switch (from.formula[0]) {
               case tc.UNIVERSAL : case tc.EXISTENTIAL : {
                  // find instance term:
                  var inst = 3; // dummy term in case this is a vacuous quantifier
                  var normMatrix = from.formula[2].normalize();
                  var instVariable = from.formula[1];
                  var a1, a2, arrs1 = [node.formula], arrs2 = [normMatrix];
                  sLoop:
                  while (a1 = arrs1.shift(), a2 = arrs2.shift()) {
                     for (var i=0; i<a2.length; i++) {
                        // ignore subformulas in which the target variable is re-bound:
                        if (a2[i].isArray && !(a2[i].length == 3 && a2[i][1] == instVariable)) {
                           arrs1.unshift(a1[i]);
                           arrs2.unshift(a2[i]);
                           continue;
                        }
                        if (a2[i] != instVariable) continue;
                        inst = a1[i];
                        break sLoop;
                     }
                  }
                  node.formula = from.formula[2].copyDeep().substitute(from.formula[1], inst);
                  tree.appendChild(par, node);
                  par = node;
                  break;
               }
               case tc.CONJUNCTION : {
                  if (from.__removeMe) {
                     if (par == from) par = from.parent;
                     node.developedFrom = from.developedFrom;
                     if (!from.isRemoved) tree.remove(from);
                  }
                  var f1 = from.formula[1].copyDeep();
                  var f2 = from.formula[2].copyDeep();

                  // I used to do:
                  // node.formula = (node.formula.equals(f1.normalize())) ? f1 : f2;
                  // but this breaks if f2.normalize() == f1.normalize() and f2 != f1,
                  // e.g. in \neg((A\land \negA)\land \neg(\negA\lor\neg\negA)).
                  // I can't store the next expansion formula in from because from can
                  // have many expansions on many branches. So instead I check for
                  // a sibling or parent node with the same from:

                  if (!node.formula.equals(f1.normalize())) node.formula = f2;
                  else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                  else { // matches both
                     node.formula = (par.developedFrom == node.developedFrom) ? f2 : f1;
                  }
                  tree.appendChild(par, node);
                  if (par.developedFrom == node.developedFrom && node.formula == f1) tree.reverse(par, node);
                  else par = node;
                  break;
               }
               case tc.DISJUNCTION : {
                  var f1 = from.formula[1].copyDeep();
                  var f2 = from.formula[2].copyDeep();
                  if (!node.formula.equals(f1.normalize())) node.formula = f2;
                  else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                  else { // matches both
                     node.formula = (par.children && par.children.length) ? f2 : f1;
                  }
                  tree.appendChild(par, node);
                  if (par.children.length == 2 && node.formula == f1) par.children.reverse();
                  par = node;
                  break;
               }
               case tc.IMPLICATION : {
                  var f1 = from.formula[1].copyDeep().negate();
                  var f2 = from.formula[2].copyDeep();
                  if (!node.formula.equals(f1.normalize())) node.formula = f2;
                  else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                  else { // matches both
                     node.formula = (par.children && par.children.length) ? f2 : f1;
                  }
                  tree.appendChild(par, node);
                  if (par.children.length == 2 && node.formula == f1) par.children.reverse();
                  par = node;
                  break;
               }
               case tc.BIIMPLICATION : {
                  var f1 = [tc.CONJUNCTION, from.formula[1], from.formula[2]].copyDeep();
                  var f2 = [tc.CONJUNCTION, from.formula[1].negate(), from.formula[2].negate()].copyDeep();
                  if (!node.formula.equals(f1.normalize())) node.formula = f2;
                  else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                  else { // matches both
                     node.formula = (par.children && par.children.length) ? f2 : f1;
                  }
                  node.__removeMe = true;
                  tree.appendChild(par, node);
                  if (par.children.length == 2 && node.formula == f1) par.children.reverse();
                  par = node;
                  break;
               }
               case tc.NEGATION : {
                  switch (from.formula[1][0]) {
                     case tc.UNIVERSAL : case tc.EXISTENTIAL : {
                        // find instance term:
                        var inst = 3; // dummy term in case this is a vacuous quantifier
                        var normMatrix = from.formula[1][2].negate().normalize();
                        var instVariable = from.formula[1][1];
                        var a1, a2, arrs1 = [node.formula], arrs2 = [normMatrix];
                        sLoop:
                        while (a1 = arrs1.shift(), a2 = arrs2.shift()) {
                           for (var i=0; i<a2.length; i++) {
                              // ignore subformulas in which the target variable is re-bound:
                              if (a2[i].isArray && !(a2[i].length == 3 && a2[i][1] == instVariable)) {
                                 arrs1.unshift(a1[i]);
                                 arrs2.unshift(a2[i]);
                                 continue;
                              }
                              if (a2[i] != instVariable) continue;
                              inst = a1[i];
                              break sLoop;
                           }
                        }
                        node.formula = from.formula[1][2].negate().copyDeep().substitute(from.formula[1][1], inst);
                        tree.appendChild(par, node);
                        par = node;
                        break;
                     }
                     case tc.CONJUNCTION : {
                        var f1 = from.formula[1][1].copyDeep().negate();
                        var f2 = from.formula[1][2].copyDeep().negate();
                        if (!node.formula.equals(f1.normalize())) node.formula = f2;
                        else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                        else { // matches both
                           node.formula = (par.children && par.children.length) ? f2 : f1;
                        }
                        tree.appendChild(par, node);
                        if (par.children.length == 2 && node.formula == f1) par.children.reverse();
                        par = node;
                        break;
                     }
                     case tc.DISJUNCTION : {
                        var f1 = from.formula[1][1].copyDeep().negate();
                        var f2 = from.formula[1][2].copyDeep().negate();
                        if (!node.formula.equals(f1.normalize())) node.formula = f2;
                        else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                        else { // matches both
                           node.formula = (par.developedFrom == node.developedFrom) ? f2 : f1;
                        }
                        tree.appendChild(par, node);
                        if (par.developedFrom == from && node.formula == f1) tree.reverse(par, node);
                        else par = node;
                        break;
                     }
                     case tc.IMPLICATION : {
                        var f1 = from.formula[1][1].copyDeep();
                        var f2 = from.formula[1][2].copyDeep().negate();
                         if (!node.formula.equals(f1.normalize())) {
                             node.formula = f2;
                         }
                         else if (!node.formula.equals(f2.normalize())) {
                             node.formula = f1;
                         }
                        else { // matches both
                           node.formula = (par.developedFrom == node.developedFrom) ? f2 : f1;
                        }
                        tree.appendChild(par, node);
                        if (par.developedFrom == from && node.formula == f1) tree.reverse(par, node);
                        else par = node;
                        break;
                     }
                     case tc.BIIMPLICATION : {
                        var f1 = [tc.CONJUNCTION, from.formula[1][1], from.formula[1][2].negate()].copyDeep();
                        var f2 = [tc.CONJUNCTION, from.formula[1][1].negate(), from.formula[1][2]].copyDeep();
                        if (!node.formula.equals(f1.normalize())) node.formula = f2;
                        else if (!node.formula.equals(f2.normalize())) node.formula = f1;
                        else { // matches both
                           node.formula = (par.children && par.children.length) ? f2 : f1;
                        }
                        node.__removeMe = true;
                        tree.appendChild(par, node);
                        if (par.children.length == 2 && node.formula == f1) par.children.reverse();
                        par = node;
                        break;
                     }
                     case tc.NEGATION : {
                        // from is doubly negated. Expand the DN node, then try again:
                        if (!from.dneTo) {
                           var newNode = new Node(from.formula[1][1].copyDeep(), from);
                           newNode.base = SenNode;
                           newNode.base();
                           newNode.developedFrom = from;
                           from.dneTo = newNode;
                           var dneToPar = (from.children[0] && from.children[0].developedFrom == from.developedFrom) ? from.children[0] : from;
                           newNode.parent = dneToPar;
                           newNode.children = dneToPar.children;
                           for (var i=0; i<newNode.children.length; i++) newNode.children[i].parent = newNode;
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
                     default : { // negated literal
                        tree.appendChild(par, node);
                        par = node;
                     }
                  }
                  break;
               }
               default : { // literal
                  tree.appendChild(par, node);
                  par = node;
               }
            }
         }
      }   
   }

   function removeUnusedNodes() {
      // If the tree os closed, the used ancestors of all complementary pairs are already 
      // marked .used, except DN formulas that didn't exist on the original tree. We mark 
      // these .used and also the other node of a used ALPHA or BETA expansion:
      if (!tree.isClosed) return;
      for (var i=0; i<tree.nodes.length; i++) {
         if (!tree.nodes[i].used) continue;
         var node = tree.nodes[i];
         if (node.formula[0] == tc.NEGATION && node.formula[1][0] == tc.NEGATION && node.children[0]) node.children[0].used = true;
         if (!node.developedFrom) continue;
         var expansion = tree.getExpansion(node);
         debug("node: "+node+", from "+node.developedFrom+" ("+node.developedFrom.type+"), from.used: "+node.developedFrom.used+", node.used: "+node.used+", expansion: "+expansion);
         for (var j=0; j<expansion.length; j++) expansion[j].used = true;
      }
      for (var i=0; i<tree.nodes.length; i++) {
         if (!tree.nodes[i].used) tree.remove(tree.nodes[i--]); // reducing i because remove() will remove it from the array
      }
   }
   
   function replaceSkolemTerms() {
      var okConstants = tree.rootNode.formula.getConstants();
      var translations = {};
      for (var n=0; n<tree.nodes.length; n++) {
         var terms = getComplexTerms(tree.nodes[n].formula);
         termLoop:
         for (var c=0; c<terms.length; c++) {
            if (okConstants.contains(terms[c][0])) continue termLoop;
            var termstr = terms[c].toString();
            debug(termstr + " is skolem term (orig terms are " + okConstants + constants +")");
            if (!translations[termstr]) {
               translations[termstr] = constants[constants.length-1] + 3;
               constants.push(translations[termstr]);
            }
            tree.nodes[n].formula.substitute(terms[c], translations[termstr], true);
         }
      }
      function getComplexTerms(formula) {
         var result = [];
         var flas = [formula];
         var fla;
         while ((fla = flas.shift())) {
            if (fla.length == 3 && fla[0] < 0) { // if fla[0] > 0 this is a term array
               if (!fla[1].isArray) { // quantified fla
                  flas.unshift(fla[2]);
                  continue;
               }
               flas.unshift(fla[1]);
               flas.unshift(fla[2]);
               continue;
            }
            if (fla[0] == tc.NEGATION) flas.unshift(fla[1]);
            else {
               for (var i=0; i<fla[1].length; i++) {
                  if (!fla[1][i].isArray) continue;
                  result.push(fla[1][i]);
                  flas.unshift(fla[1][i]);
               }
            }
         }
         return result;
      }
   }
}

SenTree.prototype.appendChild = function(oldNode, newNode) {
   debug("appending "+newNode+" to "+ oldNode); 
   if (!newNode.isSenNode) {
      newNode.base = SenNode;
      newNode.base();
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
   debug("removing " + node + " (parent: " + node.parent + ", children: " + node.children + ")");
   if (node.parent.children.length == 1) {
      node.parent.children = node.children;
      if (node.children[0]) node.children[0].parent = node.parent;
      if (node.children[1]) node.children[1].parent = node.parent;
   }
   else {
      if (node.children.length > 1) return alert("can't remove a node with two children that itself has a sibling");
      var i = (node == node.parent.children[0]) ? 0 : 1;
      if (node.children[0]) {
         node.parent.children[i] = node.children[0];
         node.children[0].parent = node.parent;
      }
      else node.parent.children.remove(node);
   }
   this.nodes.remove(node);
   node.isRemoved = true;
}

SenTree.prototype.toString = function() {
   // for debugging only
   return "<table><tr><td align='center' style='font-family:monospace'>"+getTree(this.rootNode)+"</td</tr></table>";
   function getTree(node) {
      var recursionDepth = arguments[1] || 0;
      if (++recursionDepth > 40) return "<b>...<br>[max recursion]</b>";
      var res = node + (node.closedEnd ? "<br>x<br>" : "<br>");
      if (node.children[1]) res += "<table><tr><td align='center' valign='top' style='font-family:monospace; border-top:1px solid #999; padding:3px; border-right:1px solid #999'>" + getTree(node.children[0], recursionDepth) + "</td>\n<td align='center' valign='top' style='padding:3px; border-top:1px solid #999; font-family:monospace'>" + getTree(node.children[1], recursionDepth) + "</td>\n</tr></table>";
      else if (node.children[0]) res += getTree(node.children[0], recursionDepth);
      return res;
   }
}

SenTree.prototype.substitute = function(oldTerm, newTerm) {
   for (var i=0; i<this.nodes.length; i++) {
       debug("substituting "+oldTerm+" by "+newTerm+" in "+this.nodes[i].formula);
      this.nodes[i].formula.substitute(oldTerm, newTerm);
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
   // returns all nodes that were added to the tree in the same expansion step as the given node
   if (!node.developedFrom) return [node];
   var from = node.developedFrom;
   var fromOp = from.formula[0];
   if (fromOp == tc.NEGATION) {
      // negated conjunction is treated like disjunction, etc.
      fromOp = (from.formula[1][0] == tc.CONJUNCTION) ? tc.DISJUNCTION
         : (from.formula[1][0] == tc.DISJUNCTION || from.formula[1][0] == tc.IMPLICATION) ? tc.CONJUNCTION :
         from.formula[1][0];
   }
   switch (fromOp) {
      case tc.CONJUNCTION : {
         if (node.children[0] && node.children[0].developedFrom == from) return [node, node.children[0]];
         if (node.parent.developedFrom == from) return [node.parent, node];
         return [node];
      }
      case tc.DISJUNCTION : 
      case tc.IMPLICATION : {
         return node.parent.children;
      }
      case tc.BIIMPLICATION : {
         var res = (node.children[0] && node.children[0].developedFrom == from) ? [node, node.children[0]]
            : (node.parent.developedFrom == from) ? [node.parent, node]
            : [node];
         if (!res[0].parent.children[1]) return res;
         var i = (res[0].parent.children[0] == res[0]) ? 1 : 0;
         res.push(res[0].parent.children[i]);
         if (res[0].parent.children[i].children[0] && res[0].parent.children[i].children[0].developedFrom == from) res.push(res[0].parent.children[i].children[0]);
         return res;
      }
      default : {
         return [node];
      }
   }
}

SenTree.prototype.getCounterModel = function() {
   // Read off a countermodel from an open branch.
   // First, find an open branch:
   var endNode = null;
   for (var i=0; i<this.nodes.length; i++) {
      if (this.nodes[i].children.length || this.nodes[i].closedEnd) continue;
      endNode = this.nodes[i];
      break;
   }
   if (!endNode) return null;
   debug("creating counterModel from endNode " + endNode);
   var modelFinder = new ModelFinder(this.rootNode.formula);
   var model = modelFinder.model;
   
   // set up the domain and map every term onto itself:
   var node = endNode;
   do {
      var fla = node.formula;
      while (fla[0] == tc.NEGATION) fla = fla[1]; // note that there may be unexpanded DN atoms on the branch
      if (fla[0] < 0) continue; // only consider literals
      var terms = fla[1].copy();
      for (var t=0; t<terms.length; t++) {
         var term = translator.term2html(terms[t]);
         if (model.domain.contains(term)) continue;
         debug("adding "+term);
         model.domain.push(term);
         if (terms[t].isArray) {
            for (var i=1; i<terms[t].length; i++) terms.push(terms[t][i]);
         }
         else model.interpretation[terms[t]] = term;
      }
   } while ((node = node.parent));
   if (model.domain.length == 0) model.domain = [2];
   debug("domain initialized: " + model);
   
   // interpret function and predicate symbols:
   // As for functional terms, a canonical model should assign to f^n a function F such that 
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
      while (fla[0] == tc.NEGATION) {
         fla = fla[1];
         tv = !tv;
      }
      if (fla[0] < 0) continue;
      debug("interpreting " + node);
      var pred = fla[0];
      var terms = fla[1];
      if (terms.length == 0) { // propositional constant
         model.interpretation[pred] = tv;
         continue;
      }
      // interpret function symbols:
      var subTerms = terms.copy();
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
                  for (var d=0; d<model.domain.length; d++) narrs.push(arrs[j][model.domain[d]] = []);
               }
               arrs = narrs;
            }
            for (var j=0; j<arrs.length; j++) {
               for (var d=0; d<model.domain.length; d++) arrs[j][model.domain[d]] = model.domain[0]; // default value is first individual
            }
            debug("initialized functor interpretation: " + model);
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
      if (!model.interpretation[pred]) model.interpretation[pred] = [];
      var arrs = [model.interpretation[pred]];
      for (var i=0; i<terms.length-1; i++) {
         var term = translator.term2html(terms[i]);
         if (!arrs[i][term]) arrs[i][term] = [];
         arrs[i+1] = arrs[i][term];
      }
      var lastTerm = translator.term2html(terms[terms.length-1])
      arrs[arrs.length-1][lastTerm] = tv;
      debug(model);
   } while ((node = node.parent));
   debug("model: " + model);
   if (modelFinder.isModel()) {
      debug("yep, model satisfies " + this.rootNode);
      return model;
   }
   debug("no, model doesn't satisfy " + this.rootNode);
   return null;
}

function SenNode() {
   // instances are also Nodes
   this.isSenNode = true;
   this.parent = null;
   this.children = [];
}
