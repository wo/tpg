//
// The 'translator' object is used to translate between formulas in plain text
// form and in the form used for internal computations.
//
// Internally, formulas are arrays (for performance reasons):
//
//    |~A|      => [tc.NOT, |A|]
//    |A&B|     => [tc.AND, |A|, |B|]
//    |ExA|     => [tc.SOME, |x|, |A|]
//    |Rab|     => [|R|, [|a|, |b|]]
//
// where predicates, variables and constants (including function symbols) are
// represented by integers, function terms by arrays whose first element is the
// function symbol, the other the arguments:
//
//    predicates: 1, 4, 7, ...   (n % 3 == 1)  
//    constants:  2, 5, 8, ...   (n % 3 == 2)
//    variables:  3, 6, 9, ...   (n % 3 == 0)
//    functions terms:  [2,5], [5,3,8], [8,6,[8,2]], ...
//
// The public translator methods are:
//
//    text2fla = function(str)            translates text formula -> internal
//    fla2text = function(arr)            translates internal -> text
//    sym2text = function(n)              translates internal -> text for single symbols        
//    term2text = function(arr)           translates internal -> text for a term        
//    text2sym = function(str, type)      translates individual text symbol -> internal
//

// First, some constants:
tc.register("PREDICATE");
tc.register("CONSTANT");
tc.register("VARIABLE");
tc.register("NOT");
tc.register("AND");
tc.register("OR");
tc.register("THEN");
tc.register("IFF");
tc.register("ALL");
tc.register("SOME");
tc.register("BOX");
tc.register("DIAMOND");

function Translator() {
    
    // The logical symbols used in HTML output:
    this.logSymbols = [];
    this.logSymbols[tc.NOT] = "¬";
    this.logSymbols[tc.AND] = "∧";
    this.logSymbols[tc.OR] = "∨";
    this.logSymbols[tc.THEN] = "→";
    this.logSymbols[tc.IFF] = "↔";
    this.logSymbols[tc.ALL] = "∀";
    this.logSymbols[tc.SOME] = "∃";
    this.logSymbols[tc.BOX] = "□";
    this.logSymbols[tc.DIAMOND] = "◇";
    
    // When translating internal -> text, the internal symbols are translated
    // back into the original symbol, if there is one. If not, the following
    // symbols (plus indices) are used:
    this.nonlogSymbols = [];
    this.nonlogSymbols[tc.VARIABLE]  = ["x","y","z","w","v","u","t","s"];
    this.nonlogSymbols[tc.CONSTANT]  = ["a","b","c","d","e","f","g","h","k"];
    this.nonlogSymbols[tc.PREDICATE] = ["P","Q","R","S","A","B","C","D","E"];
    
    this.error = "";  // holds the error message when a formula string could not be parsed

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
    
    this.text2fla = function(str) {
        // parse an input sentence and return internal representation.
        var boundVars = arguments[1] ? arguments[1].slice() : [];
        debug("parsing '"+str+"' (boundVars "+boundVars+")");
        
        // The next line says that any symbol except digits, brackets, %, or the
        // comma, followed by any number of digits, is allowed as
        // nonlogical expression.
  //      var re_nonlogical = /[^\d\(\)%,]\d*/g;
  //      re_nonlogical.lastIndex = 0;
        
        var reTest = /∧|∨|→|↔/.test(str);
        if (reTest) {
            // str contains a connective. Main operator might
            // nevertheless be a quantifier or negation. We replace
            // every substring in parens by "%0", "%1", etc.:
            var subStringsInParens = []; 
            var parenDepth = 0;
            var storingAtIndex = -1;
            var nstr = "";
            for (var i=0; i<str.length; i++) {
                if (str.charAt(i) == "(") {
                    parenDepth++;
                    if (parenDepth == 1) {
                        storingAtIndex = subStringsInParens.length;
                        subStringsInParens[storingAtIndex] = "";
                        nstr += "%" + storingAtIndex;
                    }
                }
                if (storingAtIndex == -1) nstr += str.charAt(i);
                else subStringsInParens[storingAtIndex] += str.charAt(i);
                if (str.charAt(i) == ")") {
                    parenDepth--;
                    if (parenDepth == 0) storingAtIndex = -1;
                }
            }
            debug("   nstr = '"+nstr+"'; ");
            
            // done. Now let's see if there is still a connective in the
            // modified string (in decreasing order or precedence):
            var reTest = nstr.match(/↔/) || nstr.match(/→/)  || nstr.match(/∨/) || nstr.match(/∧/);
            if (reTest) { 
                // yes. The matched connective is the main operator
                debug("   string is complex; ");
                var result = []; // the formula in internal format
                switch (reTest[0]) {
                    case "↔" : result[0] = tc.IFF; break;
                    case "→" : result[0] = tc.THEN; break;
                    case "∨" : result[0] = tc.OR; break;
                    case "∧" : result[0] = tc.AND; break;
                }
                debug("   main connective: "+reTest[0]+"; ");
                nstr = nstr.replace(reTest[0], "%split");
                for (var i=0; i<subStringsInParens.length; i++) {
                    nstr = nstr.replace("%"+i, subStringsInParens[i]); // restore removed substrings
                }
                var subFormulas = nstr.split("%split");
                if (!subFormulas[1]) {
                    return exit("argument missing for operator "+reTest[0]+" in "+str);
                }
                debug("   subformulas: "+subFormulas[0]+", "+subFormulas[1]+"; ");
                result.push(this.text2fla(subFormulas[0], boundVars));
                result.push(this.text2fla(subFormulas[1], boundVars));
                return this.error ? null : result;
            }
        }
        
        var reTest = str.match(/^(%neg|%Box|%Diamond)/)
        if (reTest) {
            debug("   string is negated or modal; ");
            var op = reTest[1] == '%neg' ? tc.NOT :
                reTest[1] == '%Box' ? tc.BOX : tc.DIAMOND;
            var result = [op, this.latex2fla(str.substr(reTest[1].length), boundVars)];
            return this.error ? null : result;
        }

        // if we're here the formula should be quantified or atomic
        reTest = /(%forall|%exists)([^\d\(\),%]\d*)/.exec(str);
        if (reTest && reTest.index == 0) {
            // quantified formula
            debug("   string is quantified (quantifier = '"+reTest[0]+"'); ");
            var result = [];
            result[0] = (reTest[1] == "%forall") ? tc.ALL : tc.SOME;
            if (html2symMap[reTest[2]] && this.getHtmlType(reTest[2]) != tc.VARIABLE) {
                return exit(reTest[2] + " can't be used both as variable and as " +
                            (this.getHtmlType(reTest[2]) == tc.CONSTANT ? "constant" : "predicate"));
            }
            result[1] = this.html2sym(reTest[2], tc.VARIABLE);
            if (!str.substr(reTest[0].length)) {
                return exit("There is nothing in the scope of "+str);
            }
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
                return exit(reTest[0] + " can't be used both as predicate and as " +
                            (this.getHtmlType(reTest[0]) == tc.CONSTANT ? "constant" : "variable"));
            }
            result[0] = this.html2sym(reTest[0], tc.PREDICATE);
            var termstr = str.substr(reTest.length); // empty for propositional constants
            result[1] = (termstr == '') ? [] : (parseTexTerms(termstr, boundVars) || []);
            if (arities[result[0]] !== undefined && arities[result[0]] != result[1].length) {
                return exit("Please don't use " + reTest[0] + "with varying arity. That confuses me.");
            }
            arities[result[0]] = result[1].length;
            return this.error? null : result;
        }
        
        // if the entire formula was enclosed in parens we end up here
        debug("   string could not be identified as anything;");
        if (str.match(/^\((.*)\)$/)) {
            debug("   trying again without outer parens;");
            return this.latex2fla(str.replace(/^\((.*)\)$/, "$1"), boundVars);
        }
        
        exit("Parse Error.\n'" + str + "' is not a well-formed formula.");
        
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
            else if (formula[0] < 0 && formula.length == 2) { // negated or modal
                return this.logSymbols[formula[0]] + this.fla2html(formula[1]);
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
        return (symbol % 3 == 1) ? tc.PREDICATE :
            (symbol % 3 == 2) ? tc.CONSTANT : tc.VARIABLE;
    }
    
    this.getHtmlType = function(symbol) {
        // returns the type of a HTML symbol
        symbol = html2symMap[symbol];
        if (!symbol) return null;
        return (symbol % 3 == 1) ? tc.PREDICATE :
            (symbol % 3 == 2) ? tc.CONSTANT : tc.VARIABLE;
    }
    
    function getNewSymbol(type) {
        // returns a new HTML symbol of a given type
        for (var i=0; i<translator.nonlogSymbols[type].length; i++) {
            if (!html2symMap[translator.nonlogSymbols[type][i]]) {
                return translator.nonlogSymbols[type][i];
            }
        }
        var i=2; // first subscript index
        while (html2symMap[translator.nonlogSymbols[type][0]+i]) i++;
        return translator.nonlogSymbols[type][0]+i;
    }
    
    function parseTexTerms(str, boundVars) {
        // parses a sequence of terms and returns the sequence in internal format.
        debug("parsing terms: "+str+" (boundVars "+boundVars+")");
        var nonlogical = /[^\(\),%]\d*/g;
        var result = [];
        str = str.replace(/^\((.+)\)$/, "$1"); // remove parens around arguments
        do {
            var nextTerm;
            nonlogical.lastIndex = 0;
            var reTest = nonlogical.exec(str);
            if (!reTest || reTest.index != 0) {
                return exit("I expected a (sequence of) term(s) instead of '" + str + "'");
            }
            if (translator.getHtmlType(reTest[0]) == tc.VARIABLE) { 
                if (!boundVars.includes(reTest[0])) {
                    return exit("Please don't use " + reTest[0] +
                                " both as variable and as constant. That confuses me.");
                }
                nextTerm = translator.html2sym(reTest[0], tc.VARIABLE);
            }
            else if (translator.getHtmlType(reTest[0]) == tc.PREDICATE) {
                return exit(reTest[0] + " can't be used both as individual constant and as predicate.");
            }
            else nextTerm = translator.html2sym(reTest[0], tc.CONSTANT);
            str = str.substr(reTest[0].length);
            if (str.indexOf("(") == 0) {
                // term was a function symbol. Find and parse the arguments:
                // (I can't use a simple RegExp such as /^\(([^\)]+)\)/ here because
                // I have to keep track of *how many* parens open and close,
                // cf. Rf(a)g(b) vs. Rf(a,g(b))
                var args = "", openParens = 0, spos = 0;
                do {
                    args += str.charAt(spos);
                    if (str.charAt(spos) == "(") openParens++;
                    else if (str.charAt(spos) == ")") openParens--;
                    spos++;
                } while (openParens && spos < str.length);
                debug("Arguments: "+args);
                nextTerm = [nextTerm].concat(parseTexTerms(args, boundVars));
                if (arities[reTest[0]] !== undefined && arities[reTest[0]] != nextTerm.length-1) {
                    return exit("Please don't use " + reTest[0] + " with varying arity. That confuses me.");
                }
                arities[reTest[0]] = nextTerm.length-1;
                str = str.substr(args.length);
            }
            else {
                if (arities[reTest[0]] !== undefined && arities[reTest[0]] != 0) {
                    return exit("Please don't use " + reTest[0] + " with varying arity. That confuses me.");
                }
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
