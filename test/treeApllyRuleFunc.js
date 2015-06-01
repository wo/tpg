/**

 * CONSTRUCTOR FOR NODES IN A PROOF TREES

 *    needs formulas.js

 *

 * TreeNode(formula, truthValue) - creates a new TreeNode with the given truth value

 *   .ticked                     - boolean, false if the node can still be developed

 *   .closed                     - boolean, whether the branch closes at that node

 *   .type                       - tc.CONJUNCTION or tc.NCONJUNCTION or ...

 *   .numNodes.num               - number of nodes in the entire tree

 *   .developedFrom              - TreeNode, the node from which this one was developed

 *   .parent                     - TreeNode, the node immediately above this one

 *   .children                   - TreeNode[], inverse of parent

 *   .contradictory              - defined and true iff this is a part of a contradictory pair

 *   .append(node, [developedFrom]) - appends node to this node, and marks developedFrom of node

 *   .remove()                      - removes this node from the tree

 *   .develop([termToUse])          - develops this node, using the given term (for quantified nodes)

 *   .getEndNodes()                 - returns all open endnodes below this node

 *   .getUnticked()                 - returns all unticked nodes below this node

 *   .markClosed()                  - marks the last node on any contradictory subbranch as closed

 *   .branchClosed()                - returns true if all subbranches are closed

 *   .getFormula()                  - returns the node's formula (negated if truthValue is false)

 *

 **/



tc.register("NATOMIC");

tc.register("NNEGATION");

tc.register("NCONJUNCTION");

tc.register("NDISJUNCTION");

tc.register("NIMPLICATION");

tc.register("NBIIMPLICATION");

tc.register("NUNIVERSAL");

tc.register("NEXISTENTIAL");



function TreeNode(formula, truthValue) {

	this.numNodes.num++;

	this.ticked = false;

	this.closed = false;

	this.children = new Array();

	this.parent = null;

	this.developedFrom = null;

	this.formula = formula;

	this.truthValue = truthValue;

	if (truthValue == true && formula.operator == tc.NEGATION) {

		this.formula = formula.subFormulas[0];

		this.truthValue = !truthValue;

	}

	this.type = 

		(this.formula.type == tc.ATOMIC) ? tc.ATOMIC :

		(this.formula.type == tc.QUANTIFIED) ? this.formula.quantifier :

		(this.formula.type == tc.COMPLEX) ? this.formula.operator :

		null;

	if (this.type == tc.ATOMIC) this.ticked = true;

	if (!this.truthValue) this.type = tc["N"+tc.getName(this.type)];

}



TreeNode.prototype = {

	

	numNodes : { num: 1 }, // Object, because primitive types are copied for each instance

	terms : new Array(),

	

	getFormula : function() {

		if (this.truthValue == true) return this.formula;

		else {

			var formula = new ComplexFormula();

			formula.operator = tc.NEGATION;

			formula.subFormulas[0] = this.formula;

			return formula;

		}

	},

	

	toString : function() {

		if (self.parser) return parser.getString(this.getFormula());

		else return this.getFormula();

	},

	

	appendNode : function(node, developedFrom) {

		this.children.push(node);

		node.parent = this;

		node.developedFrom = developedFrom;

	},

	

	remove : function() {

		if (!parent) return; // you can't remove the root node

		var newParentChildren = new Array();

		for (var i=0; i<this.parent.children.length; i++) {

			if (this.parent.children[i] == this) {

				for (var j=0; j<this.children.length; j++) {

					this.children[j].parent = this.parent;

					newParentChildren.push(this.children[j]);

				}

			}

			else newParentChildren.push(this.parent.children[i]);

		}

		this.parent.children = newParentChildren;

		this.numNodes.num--;

	},



/*	

	getEndNodes : function() {

		var endNodes = new Array();

		if (this.closed) return endNodes;

		if (this.children.length == 0) {

			endNodes[0] = this;

			return endNodes;

		}

		for (var i=0; i<this.children.length; i++) {

			endNodes = endNodes.concat(this.children[i].getEndNodes());

		}

		return endNodes;

	},

*/

/*	getEndNodes : function() {

		var endNodes = arguments[0] || new Array();

		if (this.closed) return;

		if (this.children.length == 0) endNodes.push(this);

		for (var i=0; i<this.children.length; i++) {

			this.children[i].getEndNodes(endNodes);

		}

		return endNodes;

	},

*/

	getEndNodes : function() {

		if (!this.previousEndNodes) this.previousEndNodes = [this];

		var endNodes = new Array();

		for (var i=0; i<this.previousEndNodes.length; i++) {

			this.previousEndNodes[i].getEndNodesReally(endNodes);

		}

		return this.previousEndNodes = endNodes;

	},

	getEndNodesReally : function(endNodes) {

		if (this.closed) return;

		if (this.children.length == 0) endNodes.push(this);

		for (var i=0; i<this.children.length; i++) {

			this.children[i].getEndNodesReally(endNodes);

		}

	},



	// returns all unticked nodes below some node

	getUnticked : function() {

		var unticked = arguments[0] || new Array();

		if (!this.ticked) unticked.push(this);

		for (var i=0; i<this.children.length; i++) {

			this.children[i].getUnticked(unticked);

		}

		return unticked;

	},



	markClosed : function() {

		var endNodes = this.getEndNodes();

		var node1, node2;

		for (var i=0; i<endNodes.length; i++) {

			if (endNodes[i].alreadyCompared) continue;

			node1 = endNodes[i];

			compareNodes: 

			do {

				node2 = node1;

				while (node2 = node2.parent) {

					if (node1.truthValue != node2.truthValue && node1.formula.equals(node2.formula)) {

						node1.contradictory = true;

						node2.contradictory = true;

						endNodes[i].closed = true;

						break compareNodes;

					}

				}

				node1.alreadyCompared = true; // prevent us from checking what has already been checked

			} while (node1 = node1.parent && !node1.alreadyCompared);

		}

	},

	

	branchClosed : function() {

		var endNodes = this.getEndNodes();

		for (var i=0; i<endNodes.length; i++) {

			if (!endNodes[i].closed) return false;

		}

		return true;

	},

	

	develop : function(termToUse) { // termToUse is only meaningful for quantified formulas

		if (this.ticked) return false;

		var endNodes = this.getEndNodes();

		if (endNodes.length == 0) return false;

		this.applyRule(this.type, endNodes, termToUse); // see below for the definition of applyRule

		this.markClosed();

		return true;

	}

	

}



TreeNode.prototype.applyRule = function(type, endNodes, termToUse) {

	if (type == tc.NNEGATION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], true);

 		endNodes[i].appendNode(node, this);

 	}

 	this.ticked = true;

 }

	else if (type == tc.CONJUNCTION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], true);

 		var node2 = new TreeNode(this.formula.subFormulas[1], true);

 		node.appendNode(node2, this);

 		endNodes[i].appendNode(node, this);

 	}

 	this.ticked = true;

 }

	else if (type == tc.NCONJUNCTION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], false);

 		var node2 = new TreeNode(this.formula.subFormulas[1], false);

 		endNodes[i].appendNode(node, this);

 		endNodes[i].appendNode(node2, this);

 	}

 	this.ticked = true;

 }

	else if (type == tc.DISJUNCTION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], true);

 		var node2 = new TreeNode(this.formula.subFormulas[1], true);

 		endNodes[i].appendNode(node, this);

 		endNodes[i].appendNode(node2, this);

 	}

 	this.ticked = true;

 }

	else if (type == tc.NDISJUNCTION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], false);

 		var node2 = new TreeNode(this.formula.subFormulas[1], false);

 		node.appendNode(node2, this);

 		endNodes[i].appendNode(node, this);

 	}

 	this.ticked = true;

 }

	else if (type == tc.IMPLICATION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], false);

 		var node2 = new TreeNode(this.formula.subFormulas[1], true);

 		endNodes[i].appendNode(node, this);

 		endNodes[i].appendNode(node2, this);

 	}

 	this.ticked = true;

 }

	else if (type == tc.NIMPLICATION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], true);

 		var node2 = new TreeNode(this.formula.subFormulas[1], false);

 		node.appendNode(node2, this);

 		endNodes[i].appendNode(node, this);

 	}

 	this.ticked = true;

 }

else if (type == tc.BIIMPLICATION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], true);

 		var node2 = new TreeNode(this.formula.subFormulas[1], true);

 		var node3 = new TreeNode(this.formula.subFormulas[0], false);

 		var node4 = new TreeNode(this.formula.subFormulas[1], false);

 		node.appendNode(node2, this);

 		node3.appendNode(node4, this);

 		endNodes[i].appendNode(node, this);

 		endNodes[i].appendNode(node3, this);

 	}

 	this.ticked = true;

 }

	else if (type == tc.NBIIMPLICATION) {

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormulas[0], true);

 		var node2 = new TreeNode(this.formula.subFormulas[1], false);

 		var node3 = new TreeNode(this.formula.subFormulas[0], false);

 		var node4 = new TreeNode(this.formula.subFormulas[1], true);

 		node.appendNode(node2, this);

 		node3.appendNode(node4, this);

 		endNodes[i].appendNode(node, this);

 		endNodes[i].appendNode(node3, this);

 	}

 	this.ticked = true;

 }

else if (type == tc.UNIVERSAL) {

 	var term = termToUse || this.findTerm();

	if (termToUse && this.usedTerms && this.usedTerms.contains(this.terms[i])) return; // no point in doing the same twice over

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), true);

 		endNodes[i].appendNode(node, this);

 	}

 }

else if (type == tc.NUNIVERSAL) {

 	var term = termToUse || this.findTerm();

	if (termToUse && this.usedTerms && this.usedTerms.contains(this.terms[i])) return; // no point in doing the same twice over

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), false);

 		endNodes[i].appendNode(node, this);

 	}

 	this.ticked = true;

 }

else if (type == tc.EXISTENTIAL) {

 	var term = termToUse || this.findTerm();

	if (termToUse && this.usedTerms && this.usedTerms.contains(this.terms[i])) return; // no point in doing the same twice over

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), true);

 		endNodes[i].appendNode(node, this);

 	}

 	this.ticked = true;

 }

else if (type == tc.NEXISTENTIAL) {

 	var term = termToUse || this.findTerm();

	if (termToUse && this.usedTerms && this.usedTerms.contains(this.terms[i])) return; // no point in doing the same twice over

 	for (var i=0; i<endNodes.length; i++) {

 		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), false);

 		endNodes[i].appendNode(node, this);

 	}

 }

}



TreeNode.prototype.findTerm = function() {

	// this.usedTerms stores all terms with which this formula has already been developed.

	// this.terms is a list of all terms currently on the tree (a property of the prototype).

	if (!this.usedTerms) this.usedTerms = new Array();

	if (this.type == tc.NEXISTENTIAL || this.type == tc.UNIVERSAL) {

		for (var i=0; i<this.terms.length; i++) {

			if (!this.usedTerms.contains(this.terms[i])) {

				this.usedTerms.push(this.terms[i]);

				return this.terms[i];

			}

		}

	}

	var t = 10000;

	while (this.terms.contains(t)) t++;

	this.terms.push(t);

	this.usedTerms.push(t);

	return t;

}

