/**
 *
 *
 **/

function ReadableFormula(str) {
	// creates a Formula (see Formula.js) first translating str into arcane notation
	
	this.translations = new Object();
	var newstr = str;
	if (str.match(/[DFGHIJLMOPQRSTVWXYZ]/)) {
		// replace F, G, b, c, x, etc by P1, P2, x1, x2, x3, etc:
		var re = new RegExp("[DFGHIJLMOPQRSTVWXYZ]\\d*", "g");
		var res, count = 1;
		while (res = re.exec(str)) {
			this.translations["P"+count] = res[0];
			newstr = newstr.replace(new RegExp(res[0], "g"), "P"+count);
			count++;
		}
		re = new RegExp("[a-z]\\d*", "g");
		count = 1;
		while (res = re.exec(str)) {
			this.translations["x"+count] = res[0];
			newstr = newstr.replace(new RegExp(res[0], "g"), "x"+count);
			count++;
		}
	}
	else {
		// replace p, q, etc. by P1x1, P1x2, etc.
		var re = new RegExp("[a-z]", "g");
		var transl, res, count = 1;
		while (res = re.exec(str)) {
			this.translations["P1x"+count] = res[0];
			newstr = newstr.replace(new RegExp(res[0], "g"), "P1x"+count);
			count++;
		}
	}
	str = newstr;

	/*
	alert("1: "+str);

	// remove whitespace:
	str = str.replace(/ /g, "");

	alert("2: "+str);

	// bring all connectives to front:
	do {
		
		str = str.replace(/(\(?
	// reintroduce missing brackets:
	str = str.replace(/([^NPax\d]|\b)([NPax\d]+[KACB][NPax\d]+)([^NPax\d]|\b)/g, "$1($2)$3");
	str = str.replace(/\(\(/g, "\(");
	str = str.replace(/\)\)/g, "\)");

	alert("3: "+str);
	
	// place connectives in front of their arguments:
	str = str.replace(/\(([^\)]+)([KACB])([^\)]+)\)/gi, "$2$1$3");
	
	alert("4: "+str);
	*/
		
	this.base = Formula;
	this.base(str);

}

ReadableFormula.prototype = new Formula();

ReadableFormula.prototype.toRString = function() {
	var str = this.toString();
	for (var t in this.translations)
		str = str.replace(this.translations[t], t);
	return str;
}

ReadableSyntax = {
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
	termRE      : /^(a|x)\d+$/,
	predicateRE : /^P\d+$/i,
	isTerm : function(str) {
		return this.termRE.test(str);
	},
	isPredicate : function(str) {
		return this.predicateRE.test(str);
	}
}

