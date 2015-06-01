/**
 *
 **/

function Formula(type) {
	// type: int
	
	this.type = type;
	this.toString = function() {
		switch (this.type) {
			case (0) :
				var ret = Formula.int2log[this.predicate];
				for (var i=0; i<this.terms.length; i++) ret+= Formula.int2log[this.terms[i]];
				return ret;
			case (2) :
				return Formula.int2log[this.quantifier] + Formula.int2log[this.variable] + this.subFormula.toString();
			case (1) :
				if (this.subFormulas.length == 1) return Formula.int2log[this.connective] + this.subFormulas[0].toString();
				if (this.subFormulas.length == 2) return "(" + this.subFormulas[0].toString() + " " + Formula.int2log[this.connective] + " " + this.subFormulas[1].toString() + ")";
				return "oops, connective with more then two arguments!";
		}
		
	}
}

Formula.prototype = {

	substitute : function(v,c) { // return fla with all free occurrences of v replaced by c
		var newFla;
		if (this.type == 0) { // atomic
			var terms = new Array();
			for (var i=0; i<this.terms.length; i++) {
				if (this.terms[i] == v) terms[i] = c;
				else terms[i] = this.terms[i];
			}
			return new AtomicFormula(this.predicate, terms);
		}
		if (this.type == 1) { // complex
			var subf = new Array();
			for (var i=0; i<this.subFormulas.length; i++) {
				subf[i] = this.subFormulas[i].substitute(v,c);
			}
			return new ComplexFormula(this.connective, subf);
		}
		if (this.type == 2) { // quantified
			if (this.variable == v) return this;
			else return new QuantifiedFormula(this.quantifier, this.variable, this.subFormula.substitute(v,c));
		}
	}
	
}

Formula.ATOMIC = 0;
Formula.COMPLEX = 1;
Formula.QUANTIFIED = 2;
Formula.int2log = [];
Formula.log2int = {};

function QuantifiedFormula(quantifier, variable, subFormula) {
	// quantifier and variable: int
	// subFormula: Formula
	
	this.base = Formula;
	this.base(Formula.QUANTIFIED);
	
	this.quantifier = quantifier;
	this.variable = variable;
	this.subFormula = subFormula;

}
QuantifiedFormula.prototype = new Formula;

function ComplexFormula(connective, subFormulas) {
	// connective: int
	// subFormulas: Formula[]
	
	this.base = Formula;
	this.base(Formula.COMPLEX);
	
	this.connective = connective;
	this.subFormulas = subFormulas;

}
ComplexFormula.prototype = new Formula;

function AtomicFormula(predicate, terms) {
	// predicate : int
	// terms: int[] (may be empty)
	// alert("creating "+predicate+terms);
	this.base = Formula;
	this.base(Formula.ATOMIC);
	
	this.predicate = predicate;
	this.terms = terms;
	// alert("new atomic : " + this);
}
AtomicFormula.prototype = new Formula;
