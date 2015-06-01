/** This script is (c) Wolfgang Schwarz 2002, wolfgang@umsu.de. **/

/**
 * This is a script that tries to create efficient tree proofs. 
 *    needs formulas.js, tree.js, parser.js, treeprinter.js
 *    outputs status messages to a function treeLog(htmlString) which has to be defined
 *
 *    A proof is started by calling makeTree(fla,nextFunc), with
 *       fla:      a Formula object
 *       nextFunc: reference to a function that should be called when finished (or stopped).
 *    The proof can be stopped by setting window.stopProof = true.
 *    The root node of the created tree will be in window.root.
 *
 **/

function makeTree(fla, nextFunc) {
	self.makeTreeNextFunc = nextFunc;
	startDate = new Date();
	// first we create a standard tree:
	makeStandardTree.start(fla, makeTree2);
}
function makeTree2(root) {
	self.root = root;
	switch (root.result) {
		case "open": treeLog("Done. Tree can't be closed."); break;
		case "timeout": treeLog("Aborted."); break;
		case "closed" : root = simplifyTree(root); 
	}
   makeTreeNextFunc();
}

// makeStandardTree.start(fla, passRootTo):
// creates a standard tree for fla, i.e. using a complete, but probably roundabout, algorithm.
// This is an object rather than just a function to allow for setTimeouts during the computation.
// passResultTo is a function that is called when computation is over, passing the root of the tree
// which has a string property called "result" holding the result.
makeStandardTree = {
	start : function(fla, passRootTo) {
		this.root = new TreeNode(fla, true);
		this.nxtFunc = passRootTo;
		this.stage = 0;
		// we cycle through these stages:
		// 1. if there is an unticked truth-functional formula, develop it and return to 1.
		// 2. if there is an unticked existential or !universal formula, develop it and return to 2.
		// 3. Develop all universal or !existential formula as often as possible, using only existing names, then return to 1.
		this.numNodes = 0;
		this.cycleLoop();
	},
	cycleLoop : function() {
		this.untickedNodes = this.root.tree.undeveloped;
		switch (this.stage) {
			case 0 :
				if (this.untickedNodes.length == 0 // all nodes developed
					|| this.numNodes == this.root.tree.num) {	// no new nodes have appeared in stages 1-3
					this.root.result = "open";
					return this.nxtFunc(this.root);
				}
				this.numNodes = this.root.tree.num;
				this.stage++;
				break;
			case 1 : case 2 :
				var node = this.getNextNode();
		 		if (!node) {
					if (this.stage == 2) this.nodeIndex = 1;
					this.stage++;
				}
				else node.develop();
				break;
			case 3 :
				var node = this.getNextNode();
		 		if (!node) this.stage = 0;
				else {
					var t;
	 				if (node.tree.terms.length==0) node.develop(); // if there are no terms so far, a new one may be used
		 			else {
						for (t=0; t<node.tree.terms.length; t++) {
		 					if (!node.usedTerms || !node.usedTerms.contains(node.tree.terms[t])) break;
						}
						if (t < node.tree.terms.length) node.develop(node.tree.terms[t]);
						else this.nodeIndex++; // node has been developed with all terms
					}
	 			}
		}
 		if (self.stopProof) {
 			this.root.result = "timeout";
 			stopProof = false;
 			return this.nxtFunc(this.root);
 		}
 		if (this.root.branchClosed) {
 			this.root.result = "closed";
 			return this.nxtFunc(this.root);
 		}
		// treeLog("creating standard tree ("+this.root.tree.num+" nodes, "+this.root.endnodes.length+" open branches, "+this.root.tree.terms.length+" constants)");
		treeLog("creating standard tree<br>("+this.root.tree.num+" nodes, "+this.untickedNodes.length+" unticked, "+this.root.tree.numOpen+" open branches, "+this.root.tree.terms.length+" constants)");
		setTimeout("makeStandardTree.cycleLoop()", 10);
	},
	order : [tc.CONJUNCTION, tc.NDISJUNCTION, tc.NIMPLICATION, tc.NNEGATION, tc.DISJUNCTION, tc.NCONJUNCTION, tc.IMPLICATION, tc.BIIMPLICATION, tc.NBIIMPLICATION],
	getNextNode : function() {
		switch (this.stage) {
			case 1 :
				for (var i=0; i<this.order.length; i++) {
					for (var j=0; j<this.untickedNodes.length; j++) {
						if (this.untickedNodes[j].type == this.order[i]) return this.untickedNodes[j];
					}
				}
				return null;
			case 2 :
				for (var j=0; j<this.untickedNodes.length; j++) {
					if (this.untickedNodes[j].type == tc.EXISTENTIAL || this.untickedNodes[j].type == tc.NUNIVERSAL) return this.untickedNodes[j];
				}
				return null;
			case 3 :
				var countIndex = 0;
				for (var j=0; j<this.untickedNodes.length; j++) {
					if (this.untickedNodes[j].type == tc.NEXISTENTIAL || this.untickedNodes[j].type == tc.UNIVERSAL) countIndex++;
					if (countIndex == this.nodeIndex) return this.untickedNodes[j];
				}
				return null;
		}				
	},
	sortCmp : function(a,b) {
		// unfortionately sorting changes the order of formulas that are equal in order (in NN4),
		// i.e. if (Fa & Ga) occurs before (Fb & GB) on the tree, it might be later in the array
		// after sorting. So formulas that are lower in the tree might be developed before formulas
		// higher up.
		return makeStandardTree.orderIndex[a.type] - makeStandardTree.orderIndex[b.type];
	}
}

// simplifyTree(rootNode):
// erases unused nodes from a closed tree
function simplifyTree(root) {
	treeLog("simplifying tree ("+root.tree.num+" nodes)");
	var endNodes = root.getAllEndNodes();
	// select all contradictory nodes:
	var usedNodes = new Array();
	for (var i=0; i<endNodes.length; i++) {
		var node = endNodes[i];
		do {
			if (node.contradictory && !usedNodes.contains(node)) usedNodes.push(node);
		} while (node = node.parent);
	}
	// extend usedNodes to include all nodes they depend on:
	for (var i=0; i<usedNodes.length; i++) {
		// alert(i+": "+parser.getString(usedNodes[i].getFormula()) + "\ndevelopedFrom: "+ (usedNodes[i].developedFrom? parser.getString(usedNodes[i].developedFrom.getFormula()) : " - ") + "\nwhich is already collected: "+ (usedNodes[i].developedFrom? usedNodes.contains(usedNodes[i].developedFrom) : " (doesn't apply) "));
		if (usedNodes[i].developedFrom && !usedNodes.contains(usedNodes[i].developedFrom)) {
			usedNodes.push(usedNodes[i].developedFrom);
		}
	}
	// usedNodes may contain too few nodes, including only half-way applied rules.
	// so we now walk through the entire tree, collect the missing nodes, and erase the rest:
	removeUselessNodes(root, usedNodes);
	treeLog("Done. Tree has "+root.tree.num+" nodes.");
	return root;
}

// This function is used by simplifyTree:
function removeUselessNodes(node, usedNodes) {
	if (!usedNodes.contains(node)                           // node is not used
		&& (!usedNodes.contains(node.developedFrom)          // and not developed from a used node
		|| node.developedFrom.formula.type == tc.QUANTIFIED)) { // or at least doesn't need to be developed from one
		node.remove();
		// node.useless = true;
	}
	for (var i=0; i<node.children.length; i++) removeUselessNodes(node.children[i], usedNodes);
}
