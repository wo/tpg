	function getInt(symbol) {
		var i = Formula.log2int[symbol];
		if (!i) {
			i = Formula.int2log.push(symbol)-1;
			Formula.log2int[symbol] = i;
		}
		return i;
	}
	

function createFormula(str) {
	// if (!confirm("create "+str)) lkjkjh();
	str = str.replace(/ /g, "");
	var comps = getComponents(str);
	// if (!confirm("comps: "+comps+ " - "+comps.length)) lkjkjh();
	if (!comps) return false;
	switch (comps[0]) {
		case (Formula.ATOMIC) :
			var predInt = getInt(comps[1]);
			var termsInt = new Array();
			for (var i=0; i<comps[2].length; i++) {
				// alert(comps[2]);
				termsInt.push(getInt(comps[2][i]));
			}
			// alert("creating atomic "+predInt+termsInt);
			return new AtomicFormula(predInt, termsInt);
		
		case (Formula.QUANTIFIED) :
			var quantInt = getInt(comps[1]);
			var varInt = getInt(comps[2]);
			var subf = createFormula(comps[3]);
			if (!subf) return false;
			return new QuantifiedFormula(quantInt, varInt, subf);
		
		case (Formula.COMPLEX) :
			var connInt = getInt(comps[1]);
			var subfs = new Array();
			for (var i=0; i<comps[2].length; i++) {
				var subf = createFormula(comps[2][i]);
				if (!subf) return false;
				subfs.push(subf);
			}
			return new ComplexFormula(connInt, subfs);
		
	}

		
	function getComponents(str) {
		// returns an array containing first the type, then
		// (case ATOMIC) the predicate, followed by an array containing the terms
		// (case QUANTIFIED) the quantifier, followed by the variable, followed by the subformula
		// (case COMPLEX) the connective, followed by an array containing the subformulas
		
		Syntax.quantifier.lastIndex = 0;
		Syntax.predicate.lastIndex = 0;
		Syntax.term.lastIndex = 0;
		
		var res = Syntax.quantifier.exec(str);
		if (res && res.index == 0) {
			// alert(str +" is quantified");
			return [Formula.QUANTIFIED, str.charAt(0), res[0].substr(1), str.substr(res[0].length)];
		}
		if (Syntax.connective.test(str)) {
			var bracketDepth = 0;
			Syntax.connective.lastIndex = 0;
			for (var i=0; i<str.length; i++) {
				if (bracketDepth == 0 && Syntax.connective.test(str.charAt(i))) {
					var subs = [str.substr(i+1)];
					if (i>0) subs.unshift(str.substr(0,i));
					// alert(str +" is complex");
					return [Formula.COMPLEX, str.charAt(i), subs];
				}
				if (str.charAt(i) == '(') bracketDepth++;
				else if (str.charAt(i) == ')') bracketDepth--;
			}
			if (!arguments[1]) return getComponents(str.replace(/^\((.+)\)$/, "$1"), 1)
			alert(str + " is not a valid complex formula");
			return null; // error
		}
		res = Syntax.predicate.exec(str);
		if (res && res.index == 0) {
			// alert(str +" is atomic");
			var ret = [Formula.ATOMIC, res[0]];
			var terms = new Array();
			str = str.substr(res.length); // for lowercase prediactes (propcal)
			while (res = Syntax.term.exec(str)) {
				// if (!confirm("term: "+res[0])) jaf();
				terms.push(res[0]);
			}
			ret.push(terms);
			return ret;
		}
		return null; // error
	}		
}


Syntax = {
	predicate   : /[DFGHIJLMNOPQRSTVWXYZ]\d*/ig,
	term        : new RegExp("[a-z]\\d*", "g"),
	bracket1	: /[\(\[]/g,
	bracket2	: /[\)\]]/g,
	connective  : /[NKACB]/g,
	quantifier  : /[UE][u-z]\d*/g,

	connectives : { 
		N : 1, 
		K : 2,
		A : 2, 
		C : 2,
		B : 2
	},
	quantifiers : {
		U : 1,
		E : 1
	},
	
}


Syntax.isPredicate = function(str) {
	return this.predicates.test(str);
};

Syntax.isTerm = function(str) {
	return this.terms.test(str);
};

Syntax.getComponents = function(atomicFormula) {
	// returns an Array containing the predicate, followed by the terms
	var comps = new Array();
}	
