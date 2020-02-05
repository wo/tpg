
function Parser() {
    // store signature info so that we can parse multiple formulas and check if
    // they make sense together (e.g. matching arities for same predicate)
    this.symbols = [];
    this.expressionType = {}; // symbol => string describing expression type
    this.arities = {}; // symbol => number
    // store whether at least one of the parsed formulas is modal/
    // propositional, so that we can build an appropriate tree/countermodel:
    this.isModal = false;
    this.isPropositional = true;
}

Parser.prototype.copy = function() {
    // returns a copy of the present parser. This allows e.g. introducing 'a' as
    // a new constant when constructing clausal normal forms, but then
    // introducing 'a' again when constructing the displayed tree: we don't have
    // to manually check where 'a' is already used.
    var nparser = new Parser(true);
    nparser.symbols = this.symbols.copy();
    for (var i=0; i<this.symbols.length; i++) {
        var sym = this.symbols[i];
        nparser.expressionType[sym] = this.expressionType[sym];
        nparser.arities[sym] = this.arities[sym];
    }
    nparser.isModal = this.isModal;
    nparser.isPropositional = this.isPropositional;
    nparser.R = this.R;
    nparser.w = this.w;
    return nparser;
}

Parser.prototype.registerExpression = function(ex, exType, arity) {
    log('registering '+exType+' '+ex);
    if (!this.expressionType[ex]) this.symbols.push(ex);
    else if (this.expressionType[ex] != exType) {
        throw "don't use '"+ex+"' as both "+this.expressionType[ex]+" and "+exType;
    }
    this.expressionType[ex] = exType;
    this.arities[ex] = arity;
}

Parser.prototype.getSymbols = function(expressionType) {
    // return all registered symbols of given type
    var res = [];
    for (var i=0; i<this.symbols.length; i++) {
        var s = this.symbols[i];
        if (this.expressionType[s].indexOf(expressionType) > -1) res.push(s);
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
    // for converting to clausal normal form (for modelfinder)
    return this.getNewSymbol('xyzwvutsr', 'variable', 0);
}

Parser.prototype.getNewFunctionSymbol = function(arity) {
    // for converting to clausal normal form (for modelfinder) 
    return this.getNewSymbol('fghijklmn', arity+"-ary function symbol", arity);
}

Parser.prototype.getNewWorldVariable = function() {
    // for standard translations: □p => ∀x(wRx ...)
    return this.getNewSymbol('wvutsr', 'world variable', 0);
}

Parser.prototype.getNewWorldName = function() {
    // for □/◇ instances in sentrees and cnf skolemization 
    return this.getNewSymbol('vutsr', 'world constant', 0);
}

Parser.prototype.getVariables = function(formula) {
    // return all variables in <formula>
    if (formula.sub) {
        return this.getVariables(formula.sub);
    }
    if (formula.sub1) {
        return this.getVariables(formula.sub1).concatNoDuplicates(
            this.getVariables(formula.sub2));
    }
    var res = [];
    var dupe = {};
    var terms = formula.isArray ? formula : formula.terms;
    for (var i=0; i<terms.length; i++) {
        if (terms[i].isArray) {
            res = res.concatNoDuplicates(this.getVariables(terms[i]));
        }
        else if (this.expressionType[terms[i]].indexOf('variable') > -1
                 && !dupe[terms[i]]) {
            dupe[terms[i]] = true;
            res.push(terms[i]);
        }
    }
    return res;
    
    // xxx del
    var res = [];
    var dupe = {};
    var num_re = /[0-9]/;
    for (var i=0; i<variables.length; i++) {
        var variable = variables[i];
        // (Make sure we don't find 'x2' if the formula contains 'x21'.)
        var pos = formula.string.indexOf(variable);
        if (pos > -1 && !num_re.test(formula[pos+1]) && !dupe[variable]) {
            dupe[variable] = true;
            res.push(variable);
        }
    }
    return res;
}

Parser.prototype.isTseitinLiteral = function(formula) {
    return this.expressionType[formula.predicate || formula.sub.predicate] == 'tseitin predicate';
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
    this.registerExpression(this.w, 'world constant', 0);
}

Parser.prototype.translateFromModal = function(formula, worldVariable) {
    // return translation of modal formula into first-order formula with
    // explicit world variables
    log("translating modal formula "+formula);
    if (!worldVariable) {
        if (!this.w) this.initModality();
        worldVariable = this.w;
    }
    if (formula.terms) { // atomic; add world variable to argument list
        var nterms = formula.terms.copyDeep();
        nterms.push(worldVariable); // don't need to add world parameters to function terms; think of 0-ary terms
        return new AtomicFormula(formula.predicate, nterms);
    }
    if (formula.quantifier) {
        var nmatrix = this.translateFromModal(formula.matrix, worldVariable);
        return new QuantifiedFormula(formula.quantifier, formula.variable, nmatrix);
        // assumes constant domains
    }
    if (formula.sub1) {
        var nsub1 = this.translateFromModal(formula.sub1, worldVariable);
        var nsub2 = this.translateFromModal(formula.sub2, worldVariable);
        return new BinaryFormula(formula.operator, nsub1, nsub2);
    }
    if (formula.operator == '¬') {
        var nsub = this.translateFromModal(formula.sub, worldVariable);
        return new NegatedFormula(nsub);
    }
    if (formula.operator == '□') {
        var newWorldVariable = this.getNewWorldVariable();
        var wRv = new AtomicFormula(this.R, [worldVariable, newWorldVariable])
        var nsub = this.translateFromModal(formula.sub, newWorldVariable);
        var nmatrix = new BinaryFormula('→', wRv, nsub);
        return new QuantifiedFormula('∀', newWorldVariable, nmatrix, true);
    }
    if (formula.operator == '◇') {
        var newWorldVariable = this.getNewWorldVariable();
        var wRv = new AtomicFormula(this.R, [worldVariable, newWorldVariable])
        var nsub = this.translateFromModal(formula.sub, newWorldVariable);
        var nmatrix = new BinaryFormula('∧', wRv, nsub);
        return new QuantifiedFormula('∃', newWorldVariable, nmatrix, true)
    }
}

Parser.prototype.stripAccessibilityClauses = function(formula) {
    // return new non-modal formula with all accessibility conditions stripped;
    // e.g. ∃v(wRv∧Av) => ∃vAv; ∀v(¬wRv∨Av) => ∀vAv. <formula> is normalized.
    log(formula);
    if (formula.quantifier) {
        var nmatrix = this.stripAccessibilityClauses(formula.matrix);
        if (nmatrix == formula.matrix) return formula;
        return new QuantifiedFormula(formula.quantifier, formula.variable, nmatrix);
    }
    if (formula.sub1) {
        if ((formula.sub1.sub && formula.sub1.sub.predicate == this.R) ||
            (formula.sub1.predicate == this.R)) {
            return this.stripAccessibilityClauses(formula.sub2);
        }
        var nsub1 = this.stripAccessibilityClauses(formula.sub1);
        var nsub2 = this.stripAccessibilityClauses(formula.sub2);
        if (formula.sub1 == nsub1 && formula.sub2 == nsub2) return formula;
        return new BinaryFormula(formula.operator, nsub1, nsub2);
    }
    if (formula.operator == '¬') {
        // negation only for literals in NNF
        return formula;
    }
    else { // atomic
        return formula;
    }
}

Parser.prototype.translateToModal = function(formula) {
    // translate back from first-order formula into modal formula, with extra
    // .world label: pv => p (v); ∀u(vRu→pu) => □p (v). Formulas of type 'wRv'
    // remain untranslated.
    log("translating "+formula+" into modal formula");
    if (formula.terms && formula.predicate == this.R) {
        return formula;
    }
    if (formula.terms) {
        // remove world variable from argument list
        var nterms = formula.terms.copyDeep();
        var worldlabel = nterms.pop();
        var res = new AtomicFormula(formula.predicate, nterms);
        res.world = worldlabel;
    }
    else if (formula.quantifier && this.expressionType[formula.variable] == 'world variable') {
        // (Ev)(wRv & Av) => <>A
        var prejacent = formula.matrix.sub2;
        var op = formula.quantifier == '∃' ? '◇' : '□';
        var res = new ModalFormula(op, this.translateToModal(prejacent));
        res.world = formula.matrix.sub1.terms[0];
    }
    else if (formula.quantifier) {
        var nmatrix = this.translateToModal(formula.matrix);
        var res = new QuantifiedFormula(formula.quantifier, formula.variable, nmatrix);
        res.world = nmatrix.world;
    }
    else if (formula.sub1) {
        var nsub1 = this.translateToModal(formula.sub1);
        var nsub2 = this.translateToModal(formula.sub2);
        var res = new BinaryFormula(formula.operator, nsub1, nsub2);
        res.world = nsub2.world; // sub1 might be 'wRv' which has no world parameter
    }
    else if (formula.operator == '¬') {
        var nsub = this.translateToModal(formula.sub);
        var res = new NegatedFormula(nsub);
        res.world = nsub.world;
    }
    return res;
}


Parser.prototype.parseInput = function(str) {
    // return [premises, conclusion] for entered string, where <premises> is
    // a list of premise Formulas and <conclusion> is a Formula.
    log("*** parsing input");
    var parts = str.split('|=');
    if (parts.length > 2) {
        throw "You can't use more than one turnstile";
    }
    var premises = [];
    var conclusion = this.parseFormula(parts[parts.length-1]);
    log("=== conclusion "+conclusion);
    if (parts.length == 2) {
        // split premises by commas that are not in parentheses:
        var temp = this.hideSubStringsInParens(parts[0]);
        var nstr = temp[0];
        var subStringsInParens = temp[1];
        var premiseStrings = nstr.split(',');
        for (var i=0; i<premiseStrings.length; i++) {
            var prem = premiseStrings[i];
            // restore substrings:
            for (var j=0; j<subStringsInParens.length; j++) {
                prem = prem.replace("%"+j, subStringsInParens[j]);
            }
            premises.push(this.parseFormula(prem));
            log("=== premise "+premises.length+": "+premises[premises.length]);
        }
    }
    return [premises, conclusion];
}

Parser.prototype.hideSubStringsInParens = function(str) {
    // return [nstr, hiddenSubStrings], where <nstr> is <str> with all
    // substrings in parentheses replaced by %0, %1, etc., and
    // <hiddenSubStrings> is a list of the corresponding substrings.
    var subStringsInParens = []; 
    var parenDepth = 0;
    var storingAtIndex = -1; // index in subStringsInParens
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
    return [nstr, subStringsInParens];
}

Parser.prototype.parseFormula = function(str) {
    // return Formula for (entered) string
    var boundVars = arguments[1] ? arguments[1].slice() : [];
    log("parsing '"+str+"' (boundVars "+boundVars+")");

    if (!arguments[1]) str = this.tidyFormula(str);

    var reTest = /∧|∨|→|↔/.test(str);
    if (reTest) {
        // str contains a connective. Main operator might nevertheless be a
        // quantifier or negation etc. We replace every substring in parens by
        // "%0", "%1", etc.:
        var temp = this.hideSubStringsInParens(str);
        var nstr = temp[0];
        var subStringsInParens = temp[1];
        log("   nstr = '"+nstr+"'; ");
         
        // Now let's see if there is still a connective in the modified string
        // (in decreasing order of precedence):
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
            var sub1 = this.parseFormula(subFormulas[0], boundVars);
            var sub2 = this.parseFormula(subFormulas[1], boundVars);
            return new BinaryFormula(op, sub1, sub2);
        }
    }
    
    var reTest = str.match(/^(¬|□|◇)/);
    if (reTest) {
        log("   string is negated or modal; ");
        var op = reTest[1];
        var sub = this.parseFormula(str.substr(1), boundVars);
        if (op == '¬') return new NegatedFormula(sub);
        this.isModal = true;
        return new ModalFormula(op, sub);
    }

    // if we're here the formula should be quantified or atomic
    reTest = /^(∀|∃)([^\d\(\),%]\d*)/.exec(str);
    if (reTest && reTest.index == 0) {
        // quantified formula
        log("   string is quantified (quantifier = '"+reTest[1]+"'); ");
        var quantifier = reTest[1];
        var variable = reTest[2];
        if (!str.substr(reTest[0].length)) {
            throw "There is nothing in the scope of "+str;
        }
        if (this.registerExpression[variable] != 'world variable') {
            this.registerExpression(variable, 'variable', 0);
        }
        boundVars.push(variable);
        this.isPropositional = false;
        var sub = this.parseFormula(str.substr(reTest[0].length), boundVars);
        return new QuantifiedFormula(quantifier, variable, sub);
    }

    // formula should be atomic
    reTest = /^[^\d\(\),%]\d*/.exec(str);
    if (reTest && reTest.index == 0) {
        // atomic
        log("   string is atomic (predicate = '"+reTest[0]+"'); ");
        var predicate = reTest[0];
        var termstr = str.substr(predicate.length); // empty for propositional constants
        var terms = this.parseTerms(termstr, boundVars) || [];
        if (termstr) {
            var predicateType = terms.length+"-ary predicate";
            if (predicate != this.R) this.isPropositional = false;
        }
        else {
            var predicateType = "proposition letter (0-ary predicate)";
        }
        this.registerExpression(predicate, predicateType, terms.length);
        return new AtomicFormula(predicate, terms);
    }

    // if the entire formula was enclosed in parens we end up here
    log("   string could not be identified as anything;");
    if (str.match(/^\((.*)\)$/)) {
        log("   trying again without outer parens;");
        return this.parseFormula(str.replace(/^\((.*)\)$/, "$1"), boundVars);
    }

    throw "Parse Error.\n'" + str + "' is not a well-formed formula.";
}        

Parser.prototype.tidyFormula = function(str) {
    // remove whitespace:
    str = str.replace(/\s/g, '');
    // replace brackets by parentheses:
    str = str.replace('[', '(').replace(']', ')');
    // check that parentheses are balanced:
    this.checkBalancedParentheses(str);
    // remove parentheses around quantifiers: (∀x)Fx => ∀xFx
    str = str.replace(/\(([∀∃]\w\d*)\)/g, '$1');
    log(str);
    return str;
}

Parser.prototype.checkBalancedParentheses = function(str) {
    // check if equally many parentheses open and close in <str>
    var openings = str.split('(').length - 1;
    var closings = str.split(')').length - 1;
    if (openings != closings) {
        throw "unbalanced parentheses: "+openings+" opening parentheses, "+closings+" closing";
    }
}  

Parser.prototype.parseAccessibilityFormula = function(str) {
    // return Formula for accessibility condition like ∀w∃v(Rwv)

    // We need to work around clashes if e.g. 'v' is already used as proposition
    // letter or 'R' as an ordinary predicate. Also need to make sure the
    // parsing of accessibility formulas doesn't set this.propositional to
    // false.
    str = str.replace('R', this.R);
    var matches = str.match(/[∀∃]./g);
    for (var i=0; i<matches.length; i++) {
        var v = matches[i][1];
        if (this.expressionType[v] && this.expressionType[v] != 'world variable') {
            var re = new RegExp(v, 'g');
            str = str.replace(re, this.getNewWorldVariable());
        }
        else {
            // also register variables as world variables:
            this.registerExpression[v] = 'world variable';
        }
    }
    var isPropositional = this.isPropositional;
    var formula = this.parseFormula(str);
    this.isPropositional = isPropositional;
    return formula;
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
