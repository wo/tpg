/**

 * CONSTRUCTOR FOR NODES IN A PROOF TREES

 *    needs formulas.js

 *

 * TreeNode(formula, truthValue)   - creates a new TreeNode with the given truth value

 *   .ticked                       - boolean, false if the node can still be developed

 *   .closed                       - boolean, whether the branch closes at that node

 *   .children                     - TreeNode[]

 *   .parent                       - TreeNode

 *   .type                         - tc.CONJUNCTION or tc.NCONJUNCTION or ...

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

	this.ticked = false;

	this.closed = false;

	this.children = new Array();

	this.parent = null;

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

	

	appendNode : function(node) {

		this.children.push(node);

		node.parent = this;

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

	getEndNodes : function() {

		var endNodes = arguments[0] || new Array();

		if (this.closed) return;

		if (this.children.length == 0) endNodes.push(this);

		for (var i=0; i<this.children.length; i++) {

			this.children[i].getEndNodes(endNodes);

		}

		return endNodes;

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

		this[this.type](endNodes, termToUse); // the prototype is used as an Array of applyRule functions (see below)

		this.markClosed();

		return true;

	}

	

}



TreeNode.prototype[tc.NNEGATION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], true);

		endNodes[i].appendNode(node);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.CONJUNCTION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], true);

		var node2 = new TreeNode(this.formula.subFormulas[1], true);

		node.appendNode(node2);

		endNodes[i].appendNode(node);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.NCONJUNCTION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], false);

		var node2 = new TreeNode(this.formula.subFormulas[1], false);

		endNodes[i].appendNode(node);

		endNodes[i].appendNode(node2);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.DISJUNCTION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], true);

		var node2 = new TreeNode(this.formula.subFormulas[1], true);

		endNodes[i].appendNode(node);

		endNodes[i].appendNode(node2);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.NDISJUNCTION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], false);

		var node2 = new TreeNode(this.formula.subFormulas[1], false);

		node.appendNode(node2);

		endNodes[i].appendNode(node);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.IMPLICATION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], false);

		var node2 = new TreeNode(this.formula.subFormulas[1], true);

		endNodes[i].appendNode(node);

		endNodes[i].appendNode(node2);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.NIMPLICATION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], true);

		var node2 = new TreeNode(this.formula.subFormulas[1], false);

		node.appendNode(node2);

		endNodes[i].appendNode(node);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.BIIMPLICATION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], true);

		var node2 = new TreeNode(this.formula.subFormulas[1], true);

		var node3 = new TreeNode(this.formula.subFormulas[0], false);

		var node4 = new TreeNode(this.formula.subFormulas[1], false);

		node.appendNode(node2);

		node3.appendNode(node4);

		endNodes[i].appendNode(node);

		endNodes[i].appendNode(node3);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.NBIIMPLICATION] = function(endNodes, termToUse) {

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormulas[0], true);

		var node2 = new TreeNode(this.formula.subFormulas[1], false);

		var node3 = new TreeNode(this.formula.subFormulas[0], false);

		var node4 = new TreeNode(this.formula.subFormulas[1], true);

		node.appendNode(node2);

		node3.appendNode(node4);

		endNodes[i].appendNode(node);

		endNodes[i].appendNode(node3);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.UNIVERSAL] = function(endNodes, termToUse) {

	var term = termToUse || this.findTerm();

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), true);

		endNodes[i].appendNode(node);

	}

}

TreeNode.prototype[tc.NUNIVERSAL] = function(endNodes, termToUse) {

	var term = termToUse || this.findTerm();

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), false);

		endNodes[i].appendNode(node);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.EXISTENTIAL] = function(endNodes, termToUse) {

	var term = termToUse || this.findTerm();

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), true);

		endNodes[i].appendNode(node);

	}

	this.ticked = true;

}

TreeNode.prototype[tc.NEXISTENTIAL] = function(endNodes, termToUse) {

	var term = termToUse || this.findTerm();

	for (var i=0; i<endNodes.length; i++) {

		var node = new TreeNode(this.formula.subFormula.substitute(this.formula.boundVariable, term), false);

		endNodes[i].appendNode(node);

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

	var t = 100;

	while (this.terms.contains(t)) t++;

	this.terms.push(t);

	this.usedTerms.push(t);

	return t;

}

