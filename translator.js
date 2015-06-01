//
// The 'translator' object is used to translate between formulas in LaTeX form, in HTML form and in 
// the form used for internal computations.
//
// Internally, formulas are arrays: 
//    |~A|      => [tc.NEGATION, |A|]
//    |A&B|     => [tc.CONJUNCTION, |A|, |B|]
//    |ExA|     => [tc.EXISTENTIAL, |x|, |A|]
//    |Rab|     => [|R|, [|a|, |b|]]
// Predicates, variables and constants (including function symbols) are represented 
// by integers, function terms by arrays whose first element is the function symbol, 
// the other the arguments:
//    predicates: 1, 4, 7, ...   (n % 3 == 1)  
//    constants:  2, 5, 8, ...   (n % 3 == 2)
//    variables:  3, 6, 9, ...   (n % 3 == 0)
//    functions:  [2,5], [5,3,8], [8,6,[8,2]], ...
//
// HTML formulas currently have a fixed form. Only the basic constituents can easily be changed by 
// changing the logSymbols and nonlogSymbols properties below.
//
// The public translator methods are:
//    latex2fla = function(str)                  translates LaTeX -> internal
//    fla2html = function(formula)               translates internal -> HTML
//    sym2html = function(internal)              translates internal -> HTML for single symbols        
//    term2html = function(internal)            translates internal -> HTML for a term        
//    html2sym = function(readable, type)        translates HTML -> internal for single symbols
//

// First, some constants:
tc.register("PREDICATE");
tc.register("CONSTANT");
tc.register("VARIABLE");
tc.register("NEGATION");
tc.register("CONJUNCTION");
tc.register("DISJUNCTION");
tc.register("IMPLICATION");
tc.register("BIIMPLICATION");
tc.register("UNIVERSAL");
tc.register("EXISTENTIAL");

function Translator() {
	
	// The logical symbols used in HTML output:
	this.logSymbols = [];
	this.logSymbols[tc.NEGATION]      = "<img src='neg.png' alt='\\neg' align='bottom'>";
	this.logSymbols[tc.CONJUNCTION]   = "<img src='wedge.png' alt='\\land' align='bottom'>";
	this.logSymbols[tc.DISJUNCTION]   = "<img src='vee.png' alt='\\lor' align='bottom'>";
	this.logSymbols[tc.IMPLICATION]   = "<img src='to.png' alt='\\to' align='bottom'>";
	this.logSymbols[tc.BIIMPLICATION] = "<img src='leftrightarrow.png' alt='\\leftrightarrow' align='bottom'>";
	this.logSymbols[tc.UNIVERSAL]     = "<img src='forall.png' alt='\\forall' align='bottom'>";
	this.logSymbols[tc.EXISTENTIAL]   = "<img src='exists.png' alt='\\exists' align='bottom'>";
	debug(this.logSymbols[tc.NEGATION] = "~", this.logSymbols[tc.CONJUNCTION] = "&amp;", this.logSymbols[tc.DISJUNCTION] = "v", this.logSymbols[tc.IMPLICATION] = "-&gt;", this.logSymbols[tc.BIIMPLICATION] = "&lt;--&gt;", this.logSymbols[tc.UNIVERSAL] = "A", this.logSymbols[tc.EXISTENTIAL] = "E", "");
	
	// When translating internal -> HTML, the internal symbols are translated back into 
	// the original symbol, if there is one.  If not, the following symbols (plus indices)
	// are used:
	this.nonlogSymbols = [];
	this.nonlogSymbols[tc.VARIABLE]  = ["x","y","z","w","v","u","t","s"];
	this.nonlogSymbols[tc.CONSTANT]  = ["a","b","c","d","e","f","g","h","k"];
	this.nonlogSymbols[tc.PREDICATE] = ["P","Q","R","S","A","B","C","D","E"];
	
	this.error = "";  // holds the error message when a LaTeX string could not be parsed
	var html2symMap;
	var sym2htmlMap;
	var arities = [];
	var translator = this;
	
	this.init = function() {
		this.error = "";
		html2symMap = {};
		sym2htmlMap = {};
		arities = [];
	}
	
	this.latex2fla = function(str) {
		// parse a first-order sentence in LaTeX encoding, returns an internal representation of the sentence.
		var boundVars = arguments[1] || [];
		debug("parsing '"+str+"' (boundVars "+boundVars+")");
		
		str = str.replace(/[{}]/g, "");           // remove curly LaTeX brackets
		str = str.replace(/\\\s/g, "")            // remove final LaTeX backslashes
		str = str.replace(/\s/g, "");             // remove whitespace
		str = str.replace(/\\/g, "%");            // replace backslash by % (backslashes cause trouble)
		str = str.replace(/%to/g, "%rightarrow"); // normalize alternative LaTeX notations
		str = str.replace(/%lor/g, "%vee");       // ...
		str = str.replace(/%land/g, "%wedge");	
		str = str.replace(/%lnot/g, "%neg");	
		
		// The next line says that any symbol except a round bracket, the comma and
		// the % sign, followed by any number of digits, is allowed as nonlogical symbol.
		// (\ is also forbidden, because \ gets translated into % below.) 
		var nonlogical = /[^\d\(\),%]\d*/g;                                nonlogical.lastIndex = 0;
		
		var reTest = /%wedge|%vee|%rightarrow|%leftrightarrow/.test(str);
		if (reTest) {
			// formula contains a connective. Main operator might nevertheless be a quantifier
			// or negation. We replace every substring in brackets by "%0", "%1", etc.:
			var subStringsInBrackets = []; 
			var bracketDepth = 0;
			var storingAtIndex = -1;
			var nstr = "";
			for (var i=0; i<str.length; i++) {
				if (str.charAt(i) == "(") {
					bracketDepth++;
					if (bracketDepth == 1) {
						storingAtIndex = subStringsInBrackets.length;
						subStringsInBrackets[storingAtIndex] = "";
						nstr += "%" + storingAtIndex;
					}
				}
				if (storingAtIndex == -1) nstr += str.charAt(i);
				else subStringsInBrackets[storingAtIndex] += str.charAt(i);
				if (str.charAt(i) == ")") {
					bracketDepth--;
					if (bracketDepth == 0) storingAtIndex = -1;
				}
			}
			debug("   nstr = '"+nstr+"'; ");
			
			// done. Now let's see if there is still a connective in the modified string:
			reTest = nstr.match(/%leftrightarrow/) || nstr.match(/%rightarrow/) || nstr.match(/%vee/) || nstr.match(/%wedge/);
			if (reTest) { 
				// yes. so the matched connective is the main operator
				debug("   string is complex; ");
				var result = []; // the formula in internal format
				switch (reTest[0]) {
					case "%leftrightarrow" : result[0] = tc.BIIMPLICATION; break;
					case "%rightarrow" : result[0] = tc.IMPLICATION; break;
					case "%vee" : result[0] = tc.DISJUNCTION; break;
					case "%wedge" : result[0] = tc.CONJUNCTION; break;
				}
				debug("   main connective: "+reTest[0]+"; ");
				nstr = nstr.replace(reTest[0], "%split");
				for (var i=0; i<subStringsInBrackets.length; i++) {
					nstr = nstr.replace("%"+i, subStringsInBrackets[i]); // restore removed substrings
				}
				var subFormulas = nstr.split("%split");
				if (!subFormulas[1]) return exit("argument missing for operator "+reTest[0]+" in "+str);
				debug("   subformulas: "+subFormulas[0]+", "+subFormulas[1]+"; ");
				result.push(this.latex2fla(subFormulas[0], boundVars));
				result.push(this.latex2fla(subFormulas[1], boundVars));
				return this.error ? null : result;
			}
			// if we're here the formula is a quantified or negated formula with complex scope
		}
		
		if (str.indexOf("%neg") == 0) {
			// this is a negated formula.
			debug("   string is negated; ");
			var result = [tc.NEGATION, this.latex2fla(str.substr(4), boundVars)];
			return this.error ? null : result;
		}
		
		// if we're here the formula should be quantified or atomic
		reTest = /(%forall|%exists)([^\d\(\),%]\d*)/.exec(str);
		if (reTest && reTest.index == 0) {
			// quantified formula
			debug("   string is quantified (quantifier = '"+reTest[0]+"'); ");
			var result = [];
			result[0] = (reTest[1] == "%forall") ? tc.UNIVERSAL : tc.EXISTENTIAL;
			if (html2symMap[reTest[2]] && this.getHtmlType(reTest[2]) != tc.VARIABLE) {
				return exit(reTest[2] + " can't be used both as variable and as " + (this.getHtmlType(reTest[2]) == tc.CONSTANT ? "constant" : "predicate"));
			}
			result[1] = this.html2sym(reTest[2], tc.VARIABLE);
			if (!str.substr(reTest[0].length)) return exit("There is nothing in the scope of "+str);
			boundVars.push(reTest[2]);
			result[2] = this.latex2fla(str.substr(reTest[0].length), boundVars);
			return this.error? null : result;
		}
		
		// formula should be atomic
		reTest = /[^\d\(\),%]\d*/.exec(str);
		if (reTest && reTest.index == 0) {
			// atomic
			debug("   string is atomic (predicate = '"+reTest[0]+"'); ");
			var result = [];
			if (html2symMap[reTest[0]] && this.getHtmlType(reTest[0]) != tc.PREDICATE) {
				return exit(reTest[0] + " can't be used both as predicate and as " + (this.getHtmlType(reTest[0]) == tc.CONSTANT ? "constant" : "variable"));
			}
			result[0] = this.html2sym(reTest[0], tc.PREDICATE);
			var termstr = str.substr(reTest.length); // empty for propositional constants
			result[1] = (termstr == '') ? [] : (parseTexTerms(termstr, boundVars) || []);
			if (arities[result[0]] !== undefined && arities[result[0]] != result[1].length) return exit("Please don't use " + reTest[0] + "with varying arity. That confuses me.");
			arities[result[0]] = result[1].length;
			return this.error? null : result;
		}
		
		// if the entire formula was enclosed in brackets we end up here
		debug("   string could not be identified as anything;");
		if (str.match(/^\((.*)\)$/)) {
			debug("   trying again without outer brackets;");
			return this.latex2fla(str.replace(/^\((.*)\)$/, "$1"), boundVars); // remove outer brackets
		}
		
		exit("Parse Error.\n'" + str + "' is not a well-formed formula.");
		
		/*
		function getBalancedSubstring(str, startPosition, endChar) {
			var startChar = str.charAt(startPosition);
			var res = "";
			var depth = 1;
			var pos = startPosition + 1; 
			while (pos < str.length) {
				if (str.charAt(pos) == endChar) {
					depth--;
					if (depth == 0) break;
				}
				else if (str.charAt(pos) == startChar) depth++;
				res += str.charAt(pos);
				pos++;
			}
			return res;
		}
		*/
	}
	
	this.fla2html = function(formula) {
		// returns the HTML string for an internal formula
		try {
			if (formula.length == 3) {
				if (!formula[1].isArray) { // fla is quantified
					var str = this.logSymbols[formula[0]];
					str += this.sym2html(formula[1]);
					str += this.fla2html(formula[2]);
					return str;
				}
				var str = "(";
				str += this.fla2html(formula[1]);
				str += this.logSymbols[formula[0]];
				str += this.fla2html(formula[2]);
				str += ")";
				return str;
			}
			if (formula[0] == tc.NEGATION) {
				return this.logSymbols[tc.NEGATION] + this.fla2html(formula[1]);
			}
			var str = this.sym2html(formula[0]);
			for (var i=0; i<formula[1].length; i++) str += this.term2html(formula[1][i]);
			return str;
		}
		catch(e) {
			// This should never happen, but often does when I tweak the code.
			debug("ERROR: fla2html called for " + formula + ", which is not a formula: " + e);
			return "?"; 
		}
	}
		
	this.term2html = function(term) {
		if (!term.isArray) return this.sym2html(term);
		var args = [];
		for (var i=1; i<term.length; i++) {
			args.push(term[i].isArray ? this.term2html(term[i]) : this.sym2html(term[i]));
		}
		return this.sym2html(term[0]) + "(" + args.join(",") + ")";
	}

	this.sym2html = function(internal) {
		// return output counterpart of internal symbol
		if (sym2htmlMap[internal]) return sym2htmlMap[internal];
		// if (internal == tc.IDENTITY) return "=";
		// find new readable symbol:
		var type = this.getType(internal);
		if (!type) return null;
		var readable = getNewSymbol(type);
		html2symMap[readable] = internal;
		sym2htmlMap[internal] = readable;
		return readable;
	}
	
	this.html2sym = function(readable, type) {
		// returns internal counterpart of a symbol
		if (html2symMap[readable]) return html2symMap[readable];
		// find new internal symbol:
		var internal = (type == tc.PREDICATE) ?  4 : // 1 = equals
			(type == tc.CONSTANT) ? 2 :
			(type == tc.VARIABLE) ? 3 : 
			exit("unknown type: "+type);
		while (sym2htmlMap[internal]) internal += 3;
		html2symMap[readable] = internal;
		sym2htmlMap[internal] = readable;
		return internal;
	}
	
	this.getType = function(symbol) {
		// returns the type of an internal symbol
		return (symbol % 3 == 1) ? tc.PREDICATE : (symbol % 3 == 2) ? tc.CONSTANT : tc.VARIABLE;
	}
	
	this.getHtmlType = function(symbol) {
		// returns the type of a HTML symbol
		symbol = html2symMap[symbol];
		if (!symbol) return null;
		return (symbol % 3 == 1) ? tc.PREDICATE : (symbol % 3 == 2) ? tc.CONSTANT : tc.VARIABLE;
	}
	
	function getNewSymbol(type) {
		// returns a new HTML symbol of a given type
		for (var i=0; i<translator.nonlogSymbols[type].length; i++) {
			if (!html2symMap[translator.nonlogSymbols[type][i]]) return translator.nonlogSymbols[type][i];
		}
		var i=2; // first subscript index
		while (html2symMap[translator.nonlogSymbols[type][0]+i]) i++;
		return translator.nonlogSymbols[type][0]+i;
	}
	
	function parseTexTerms(str, boundVars) {
		debug("parsing terms: "+str+" (boundVars "+boundVars+")");
		// parses a sequence of terms and returns the sequence in internal format.
		var nonlogical = /[^\(\),%]\d*/g;
		var result = [];
		str = str.replace(/^\((.+)\)$/, "$1"); // remove brackets around arguments
		do {
			var nextTerm;
			nonlogical.lastIndex = 0;
			var reTest = nonlogical.exec(str);
			if (!reTest || reTest.index != 0) return exit("I expected a (sequence of) term(s) instead of '" + str + "'");
			if (translator.getHtmlType(reTest[0]) == tc.VARIABLE) { 
				if (!boundVars.contains(reTest[0])) return exit("Please don't use " + reTest[0] + " both as variable and as constant. That confuses me.");
				nextTerm = translator.html2sym(reTest[0], tc.VARIABLE);
			}
			else if (translator.getHtmlType(reTest[0]) == tc.PREDICATE) return exit(reTest[0] + " can't be used both as individual constant and as predicate.");
			else nextTerm = translator.html2sym(reTest[0], tc.CONSTANT);
			str = str.substr(reTest[0].length);
			if (str.indexOf("(") == 0) {
				// term was a function symbol. Find and parse the arguments:
				// (I can't use a simple RegExp such as /^\(([^\)]+)\)/ here because I have to keep track
				// of *how many* brackets open and close, cf. Rf(a)g(b) vs. Rf(a,g(b))
				var args = "", openBrackets = 0, spos = 0;
				do {
					args += str.charAt(spos);
					if (str.charAt(spos) == "(") openBrackets++;
					else if (str.charAt(spos) == ")") openBrackets--;
					spos++;
				} while (openBrackets && spos < str.length);
				debug("Arguments: "+args);
				nextTerm = [nextTerm].concat(parseTexTerms(args, boundVars));
				if (arities[reTest[0]] !== undefined && arities[reTest[0]] != nextTerm.length-1) return exit("Please don't use " + reTest[0] + " with varying arity. That confuses me.");
				arities[reTest[0]] = nextTerm.length-1;
				str = str.substr(args.length);
			}
			else {
				if (arities[reTest[0]] !== undefined && arities[reTest[0]] != 0) return exit("Please don't use " + reTest[0] + " with varying arity. That confuses me.");
				arities[reTest[0]] = 0;
			}
			result.push(nextTerm);
			if (str.indexOf(",") == 0) str = str.substr(1);
		} while (str.length > 0);
		return result;
	}
	
	function exit(str) {
		// This function is called in case of a LaTeX parse error
		if (translator.error) return; // ignore follow-up errors
		translator.error = str.replace(/%/g,"\\");
		debug("Parse Error!");
		debug(translator.error);
	}
	
}

translator = new Translator();
