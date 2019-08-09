
function Parser() {
    // store signature info so that we can parse multiple formulas and check if
    // they make sense together (e.g. matching arities for same predicate); free
    // variables and skolem terms used in tableau construction are not
    // registered here, but skolem terms used for CNF conversion are. 
    this.symbols = [];
    this.expressionType = {};
    this.arities = {};
    // store whether at least one of the parsed formulas is modal or
    // propositional, so that we can build an appropriate tree/countermodel:
    this.isModal = false;
    this.translatedFromModal = false;
    this.isPropositional = true;
    // When operating on a formula, it's useful to know what's a predicate or a
    // variable etc.; the following line makes the information in Parser()
    // available through formula.parser. Note that this will break if we
    // simultaneously operate on formulas created from different Parsers.
    Formula.prototype.parser = this;
}

Parser.prototype.registerExpression = function(ex, exType, arity) {
    log('registering '+exType+' '+ex);
    if (!this.expressionType[ex]) this.symbols.push(ex);
    else if (this.expressionType[ex] != exType) {
        throw "don't use '"+ex+"' as both "+this.expressionType[ex]+" and "+exType;
    }
    this.expressionType[ex] = exType;
    this.arities[ex] = arity;
    // xxx del if (ex == this.freeVariable) this.freeVariable = 'ξ';
}

Parser.prototype.getSymbols = function(expressionType) {
    // return all registered symbols of given type
    var res = [];
    for (var i=0; i<this.symbols.length; i++) {
        var s = this.symbols[i];
        if (this.expressionType[s] == expressionType) res.push(s);
    }
    return res;
}

Parser.prototype.getNewSymbol = function(candidates, expressionType, arity) {
    // returns new symbol of given type and arity from <candidates> (string!)
    var candidates = candidates.split('');
    for (var i=0; i<candidates.length; i++) {
        var sym = candidates[i];
        if (!this.expressionType[sym]) {
            this.registerExpression(sym, expressionType, arity);
            return sym;
        }
        // after we've gone through <candidates>, add indices to first element:
        candidates.push(candidates[0]+(i+2));
    }
}

Parser.prototype.getNewConstant = function() {
    // for gamma/delta instances in sentrees and cnf skolemization
    return this.getNewSymbol('abcdefghijklmno', 'individual constant', 0);
}

Parser.prototype.getNewVariable = function() {
    // for converting to prenex/clausal normal form (for modelfinder)
    return this.getNewSymbol('xyzwvutsr', 'variable', 0);
}

Parser.prototype.getNewFunctionSymbol = function(arity) {
    // for converting to prenex/clausal normal form (for modelfinder) 
    return this.getNewSymbol('fghijklmn', arity+"-ary function symbol", arity);
}

Parser.prototype.getNewWorldVariable = function() {
    // for standard translations: □p => ∀x(wRx ...)
    return this.getNewSymbol('wvuts', 'world variable', 0);
}

Parser.prototype.getNewWorldName = function() {
    // for □/◇ instances in sentrees and cnf skolemization 
    return this.getNewSymbol('wvutsrqponmlkjihgfedcba', 'world constant', 0);
}

Parser.prototype.initModality = function() {
    // convert signature to standard translation and initialize extra modal
    // vocabulary
    for (var i=0; i<this.symbols.length; i++) {
        var sym = this.symbols[i];
        if (this.expressionType[sym].indexOf('predicate') > -1) {
            this.arities[sym] += 1;
        }
    }
    // This assumes initModality() is called after all formulas have been
    // parsed.
    this.R = this.getNewSymbol('Rrℜ', '2-ary predicate', 2);
    this.w = this.getNewSymbol('wvur', 'world constant', 0);
    this.translatedFromModal = true;
}


Parser.prototype.parseFormula = function(str) {
    // return Formula for string
    var isAccessibilityFormula = arguments[1];
    var boundVars = arguments[2] ? arguments[2].slice() : [];
    log("parsing '"+str+"' (boundVars "+boundVars+")");
    str = str.trim();

    var reTest = /∧|∨|→|↔/.test(str);
    if (reTest) {
        // str contains a connective. Main operator might nevertheless be a
        // quantifier or negation etc. We replace every substring in parens by
        // "%0", "%1", etc.:
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
        log("   nstr = '"+nstr+"'; ");
         
        // done. Now let's see if there is still a connective in the
        // modified string (in decreasing order of precedence):
        var reTest = nstr.match(/↔/) || nstr.match(/→/)  || nstr.match(/∨/) || nstr.match(/∧/);
        if (reTest) { 
            // yes. The matched connective is the main operator
            log("   string is complex; ");
            var op = reTest[0];
            log("   main connective: "+op+"; ");
            nstr = nstr.replace(op, "%split");
            // restore removed substrings:
            for (var i=0; i<subStringsInParens.length; i++) {
                nstr = nstr.replace("%"+i, subStringsInParens[i]);
            }
            var subFormulas = nstr.split("%split");
            if (!subFormulas[1]) {
                throw "argument missing for operator "+op+" in "+str;
            }
            log("   subformulas: "+subFormulas[0]+", "+subFormulas[1]+"; ");
            var sub1 = this.parseFormula(subFormulas[0], isAccessibilityFormula, boundVars);
            var sub2 = this.parseFormula(subFormulas[1], isAccessibilityFormula, boundVars);
            return new BinaryFormula(op, sub1, sub2, this);
        }
    }
    
    var reTest = str.match(/^(¬|□|◇)/);
    if (reTest) {
        log("   string is negated or modal; ");
        var op = reTest[1];
        var sub = this.parseFormula(str.substr(1), isAccessibilityFormula, boundVars);
        if (op == '¬') return new NegatedFormula(sub, this);
        else return new ModalFormula(op, sub, this);
    }

    // if we're here the formula should be quantified or atomic
    reTest = /^(∀|∃)([^\d\(\),%]\d*)/.exec(str);
    if (reTest && reTest.index == 0) {
        // quantified formula
        log("   string is quantified (quantifier = '"+reTest[1]+"'); ");
        var quantifier = reTest[1];
        var variable = reTest[2];
        if (!isAccessibilityFormula) this.registerExpression(variable, 'variable');
        if (!str.substr(reTest[0].length)) {
            throw "There is nothing in the scope of "+str;
        }
        boundVars.push(variable);
        var sub = this.parseFormula(str.substr(reTest[0].length), isAccessibilityFormula, boundVars);
        return new QuantifiedFormula(quantifier, variable, sub, this);
    }

    // formula should be atomic
    reTest = /^[^\d\(\),%]\d*/.exec(str);
    if (reTest && reTest.index == 0) {
        // atomic
        log("   string is atomic (predicate = '"+reTest[0]+"'); ");
        if (isAccessibilityFormula) {
            var predicate = this.R;
            var terms = [str[1], str[2]];
            this.registerExpression(str[1], 'world variable', 0);
            this.registerExpression(str[2], 'world variable', 0);
            return new AtomicFormula(predicate, terms, this);
        }
        var predicate = reTest[0];
        var termstr = str.substr(predicate.length); // empty for propositional constants
        var terms = this.parseTerms(termstr, boundVars) || [];
        var predicateType = terms ? terms.length+"-ary predicate" : "proposition letter (0-ary predicate)";
        this.registerExpression(predicate, predicateType, terms.length);
        return new AtomicFormula(predicate, terms, this);
    }

    // if the entire formula was enclosed in parens we end up here
    log("   string could not be identified as anything;");
    if (str.match(/^\((.*)\)$/)) {
        log("   trying again without outer parens;");
        return this.parseFormula(str.replace(/^\((.*)\)$/, "$1"), isAccessibilityFormula, boundVars);
    }

    throw "Parse Error.\n'" + str + "' is not a well-formed formula.";
}        

Parser.prototype.parseAccessibilityFormula = function(str) {
    // return Formula for accessibility condition like ∀w∃v(Rwv)
    return this.parseFormula(str, true);
}

Parser.prototype.parseTerms = function(str, boundVars) {
    // parses a sequence of terms and returns the sequence in internal format,
    // as nested array
    log("parsing terms: "+str+" (boundVars "+boundVars+")");
    if (!str) return [];
    var result = [];
    str = str.replace(/^\((.+)\)$/, "$1"); // remove surrounding parens
    do {
        var reTest = /[^\(\),%]\d*/.exec(str);
        if (!reTest || reTest.index != 0) {
            throw "I expected a (sequence of) term(s) instead of '" + str + "'";
        }
        var nextTerm = reTest[0];
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
            log("Arguments: "+args);
            nextTerm = [nextTerm].concat(this.parseTerms(args, boundVars));
            var arity = (nextTerm.length - 1);
            this.registerExpression(reTest[0], arity+"-ary function symbol", arity);
            str = str.substr(args.length);
        }
        else if (!boundVars.includes(nextTerm)) {
            this.registerExpression(nextTerm, 'individual constant', 0);
        }
        result.push(nextTerm);
        if (str.indexOf(",") == 0) str = str.substr(1);
    } while (str.length > 0);
    return result;
}
