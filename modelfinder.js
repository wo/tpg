
/**
 * Often there are simple countermodels that are hard to find through the tree
 * method; so we run a separate algorithm to find countermodels.
 * 
 * In outline, this works as follows.
 * 
 * 1. We transform the (demodalized) formulas for which we want to find a model
 *    into clausal normal form, using prenexing and skolemization to remove
 *    quantifiers. A CNF is a conjunction (represented as a list) of
 *    disjunctions ("clauses", also lists). Free variables are read as
 *    universal.
 * 
 * 2. We now start with a domain of size 1, namely { 0 }. We add further
 *    elements until a model is found. For each domain, we do the following:
 * 
 * 3. We replace free (i.e. universal) variables in the list of clauses by
 *    numbers. So for domain { 0,1 }, [Fx] would be replaced by two clauses,
 *    [F0] and [F1].
 * 
 * 4. We process the list of clauses from left to right, starting with an empty
 *    interpretation relative to which all literals are neither true nor false.
 *    At each step, we look at one literal in one clause, with the aim of making
 *    it true. If it can't be made true, we remove it from the clause list. If
 *    it can be made true, we simplify the remaining clauses by substituting all
 *    occurrences of newly interpreted terms by their values (e.g. turning Ac
 *    into A0), removing clauses for which any literal is settled true, and
 *    removing literals that are settled false.
 * 
 * Models for originally modal formulas (which we recognize from parser.isModal
 * == true) have two domains, W and D. The elements of W are also natural
 * numbers starting with 0. Accessibility conditions like reflexivity are added
 * to the formulas for which we want to find a model. In modal models, all
 * predicates take a world as their last argument; 'R' takes two worlds,
 * function terms only take individuals.
 */

function ModelFinder(initFormulas, parser, accessibilityConstraints, s5) {
    /**
     * Prototype for a modelfinder
     * 
     * <initFormulas> is a list of demodalized formulas in NNF for which we try
     * to find a model; <accessibilityConstraints> is another such list, for
     * modal models; <s5> is boolean.
     */
    log("*** creating ModelFinder");
    
    this.parser = parser;
    this.s5 = s5;
    
    if (s5) {
        accessibilityConstraints = [];
        initFormulas = initFormulas.map(function(f) {
            return parser.stripAccessibilityClauses(f);
        });
    }
    
    // collect expressions whose interpretation should be displayed in the
    // model (before adding skolem terms):
    this.predicates = parser.getSymbols('predicate');
    if (s5) this.predicates.remove(parser.R);
    this.constants = parser.getSymbols('individual constant');
    this.funcSymbols = parser.getSymbols('function symbol');
    if (parser.isModal) {
        this.constants.unshift(parser.w);
    }
    
    // break down initFormulas and accessibilityConstraints into clauses:
    initFormulas = initFormulas.concat(accessibilityConstraints || []);
    this.clauses = this.getClauses(initFormulas);
    
    // initialize model:
    var numIndividuals = 1;
    var numWorlds = this.parser.isModal ? 1 : 0;
    this.model = new Model(this, numIndividuals, numWorlds);
    
    // set up list of alternative models for backtracking
    this.alternativeModels = [];
}

ModelFinder.prototype.getClauses = function(formulas) {
    /**
     * convert <formulas> into clausal normal form and return combined list of
     * clauses.
     *
     * A clausal normal form is a list (interpreted as conjunction) of
     * "clauses", each of which is a list (interpreted as disjunction) of
     * literals. Variables are understood as universal; existential quantifiers
     * are skolemized away.
     */
    var res = [];
    for (var i=0; i<formulas.length; i++) {
        var formula = formulas[i]; 
        log('getting clauses from '+formula);
        var distinctVars = this.makeVariablesDistinct(formula);
        log('distinctVars: '+distinctVars);
        var skolemized = this.skolemize(distinctVars);
        log('skolemized: '+skolemized);
        var quantifiersRemoved = skolemized.removeQuantifiers();
        log('qantifiers removed: '+quantifiersRemoved);
        var clauses = this.tseitinCNF(quantifiersRemoved);
        // var clauses = this.cnf(quantifiersRemoved);
        log('cnf: '+clauses);
        res.extendNoDuplicates(clauses);
    }
    // order clauses by length (number of disjuncts):
    res.sort(function(a,b){ return a.length - b.length; });
    log('all clauses: '+res);
    res = this.simplifyClauses(res);
    log('simplified clauses: '+res);
    return res;
}

ModelFinder.prototype.makeVariablesDistinct = function(formula) {
    /**
     * return an equivalent variant of <formula> that doesn't reuse the same
     * variable (for conversion to prenex normal form); <formula> must be in
     * NNF.
     */
    var usedVariables = arguments[1] || [];
    var parser = this.parser;
    // log('making variables distinct in '+formula+' (used '+usedVariables+')');
    if (formula.matrix) {
        var nmatrix = formula.matrix;
        var nvar = formula.variable;
        if (usedVariables.includes(formula.variable)) {
            // log('need new variable instead of '+formula.variable);
            nvar = parser.expressionType[nvar] == 'world variable' ?
                parser.getNewWorldVariable() : parser.getNewVariable();
            nmatrix = nmatrix.substitute(formula.variable, nvar);
        }
        usedVariables.push(nvar);
        nmatrix = this.makeVariablesDistinct(nmatrix, usedVariables);
        // log('back at '+formula+': new matrix is '+nmatrix);
        if (nmatrix == formula.matrix) return formula;
        return new QuantifiedFormula(formula.quantifier, nvar, nmatrix, formula.overWorlds);
    }
    if (formula.sub1) {
        var nsub1 = this.makeVariablesDistinct(formula.sub1, usedVariables);
        var nsub2 = this.makeVariablesDistinct(formula.sub2, usedVariables);
        if (formula.sub1 == nsub1 && formula.sub2 == nsub2) return formula;
        return new BinaryFormula(formula.operator, nsub1, nsub2);
    }
    // literal:
    return formula;
}

ModelFinder.prototype.skolemize = function(formula) {
    /**
     * return <formula> with existential quantifiers skolemized away
     */
    log('skolemizing '+formula);
    var boundVars = arguments[1] ? arguments[1].copy() : [];
    // log(formula.string+' bv: '+boundVars);
    var parser = this.parser;
    if (formula.quantifier == '∃') {
        // skolemize on variables that are bound at this point and that occur in
        // the matrix (ignoring formula.variable)
        var skolemVars = [];
        boundVars.forEach(function(v) {
            if (formula.matrix.string.indexOf(v) > -1) skolemVars.push(v);
        });
        var isWorldType = parser.expressionType[formula.variable] == 'world variable';
        var skolemTerm;
        if (skolemVars.length > 0) {
            var funcSymbol = parser.getNewFunctionSymbol(skolemVars.length, isWorldType);
            var skolemTerm = skolemVars;
            skolemTerm.unshift(funcSymbol);
        }
        else skolemTerm = isWorldType ? parser.getNewWorldName() : parser.getNewConstant();
        var nmatrix = formula.matrix.substitute(formula.variable, skolemTerm); 
        // nmatrix.constants.push(skolemVars.length > 0 ? funcSymbol : skolemTerm);
        nmatrix = this.skolemize(nmatrix, boundVars);
        return nmatrix;
    }
    if (formula.quantifier) { // ∀
        boundVars.push(formula.variable);
        var nmatrix = this.skolemize(formula.matrix, boundVars);
        if (nmatrix == formula.matrix) return formula;
        return new QuantifiedFormula(formula.quantifier, formula.variable, nmatrix,
                                     formula.overWorlds);
    }
    if (formula.sub1) {
        var nsub1 = this.skolemize(formula.sub1, boundVars);
        var nsub2 = this.skolemize(formula.sub2, boundVars);
        if (formula.sub1 == nsub1 && formula.sub2 == nsub2) return formula;
        return new BinaryFormula(formula.operator, nsub1, nsub2);
    }
    // literal:
    return formula;
}

ModelFinder.prototype.tseitinCNF = function(formula) {
    /**
     * convert <formula> into CNF.
     *
     * We use a kind of tseitin transform to keep the number of clauses under
     * control. To construct the tseitin transform of a propositional formula F,
     * we introduce a new sentence letter $ for each non-atomic subformula of F
     * and list the equivalences between $ and the relevant subformula, with
     * non-trivial subsubformulas replaced by their tseitin letters. E.g., for F
     * = p -> ~q, we would list
     * 
     *    $ <-> ~q
     *    $' <-> (p -> $1).
     * 
     * The tseitin transform of F is the tseitin letter for the whole formula
     * conjoined with the equivalences:
     * 
     *    $' & ($ <-> ~q) & ($' <-> (p -> $)).
     *
     * The tseitin CNF converts this into a conjunction of disjunctions.
     *
     * We have to be careful with free variables. Consider ∃xFx → ∃xGx.
     * Skolemized, this becomes ¬Fx ∨ Ga. The tseitin CNF of that is
     *
     * ($ ↔ ¬Fx) ∧ ($ ∨ Ga).
     *
     * If we create the instantiances of this universal requirement for all
     * members of domain { 0,1 }, we get
     *
     * ($ ↔ ¬F0) ∧ ($ ∨ Ga) and
     * ($ ↔ ¬F1) ∧ ($ ∨ Ga),
     *
     * which wrongly requires F0 ↔ F1. So we don't use new proposition letters
     * $, but first-order formulas: with $x instead of $, the transform is
     * 
     * ($x ↔ ¬Fx) ∧ ($x ∨ Ga).
     *
     * The instances are
     *
     * ($0 ↔ ¬F0) ∧ ($0 ∨ Ga) and
     * ($1 ↔ ¬F1) ∧ ($1 ∨ Ga).
     * 
     */
    if (formula.type == 'literal') {
        return [[formula]];
    }

    log('creating tseitin transform of '+formula);
    // collect all non-atomic subformulas:
    var subformulas = this.tseitinSubFormulas([formula]).removeDuplicates();
    // sort by increasing complexity:
    subformulas.sort(function(a,b) {
        return tseitinComplexity(a) - tseitinComplexity(b);
    });
    // Now introduce a new atomic formula for each non-literal subformula.
    if (!this.tseitsinFormulas) {
        this.tseitsinFormulas = {}; // subformula => formula, so that we use the
                                    // same tseitsin formula for the same
                                    // subformula in different <formula>s
    }
    var clauses = [];
    while (subformulas.length) {
        var subf = subformulas.shift();
        log('  subformula '+subf)
        var p = this.tseitsinFormulas[subf.string];
        if (!p) {
            var vars = this.parser.getVariables(subf); // optimise!
            var pSym = this.parser.getNewSymbol('$', 'tseitin predicate', vars.length);
            p = new AtomicFormula(pSym, vars);
            this.tseitsinFormulas[subf.string] = p;
            // add 'p <-> S':
            var bicond = new BinaryFormula('↔', p, subf);
            clauses.extendNoDuplicates(this.cnf(bicond));
            log('  adding clause for '+bicond+': '+clauses);
        }
        // else log('subformula already known');
        if (subformulas.length == 0) {
            // add p itself:
            clauses.extendNoDuplicates([[p]]);
            log('  adding tseitin formula '+p);
        }
        // replace all occurrences of sentence in the list by p:
        for (var i=0; i<subformulas.length; i++) {
            subformulas[i] = this.tseitinReplace(subformulas[i], subf, p);
        }
    }
    clauses.sort(function(a,b){ return a.length - b.length; });
    return clauses;

    function tseitinComplexity(formula) {
        // return degree of complexity of <formula>, for sorting
        if (formula.sub) {
            return 1 + tseitinComplexity(formula.sub);
        }
        if (formula.sub1) {
            return 1 + Math.max(tseitinComplexity(formula.sub1),
                                tseitinComplexity(formula.sub2));
        }
        return 0;
    }

}

ModelFinder.prototype.tseitinSubFormulas = function(formulas) {
    /**
     * return non-literal subformulas of <formulas>
     */
    var res = []
    for (var i=0; i<formulas.length; i++) {
        if (formulas[i].type != 'literal') {
            var subformulas = formulas[i].sub ? [formulas[i].sub] :
                formulas[i].sub1 ? [formulas[i].sub1, formulas[i].sub2] : null;
            res.extend(this.tseitinSubFormulas(subformulas));
            res.unshift(formulas[i]);
        }
    }
    return res;
}

ModelFinder.prototype.tseitinReplace = function(formula, f1, f2) {
    /**
     * replace all occurrences of <f1> in <formula> by <f2>:
     */
    if (formula.equals(f1)) return f2;
    if (formula.sub) {
        var nsub = this.tseitinReplace(formula.sub, f1, f2);
        if (nsub == formula.sub) return formula;
        return new NegatedFormula(nsub);
    }
    if (formula.sub1) {
        var nsub1 = this.tseitinReplace(formula.sub1, f1, f2);
        var nsub2 = this.tseitinReplace(formula.sub2, f1, f2);
        if (formula.sub1 == nsub1 && formula.sub2 == nsub2) return formula;
        return new BinaryFormula(formula.operator, nsub1, nsub2);
    }
    return formula;
}

ModelFinder.prototype.cnf = function(formula) {
    /**
     * convert <formula> to CNF; formula need not be in NNF (because of tseitin
     * transformations)
     */
    if (formula.type == 'literal') {
        // return CNF with 1 clause containing 1 literal:
        return [[formula]];
    }
    // optimize: remove creation of negated formulas through negate() etc.?
    var con, dis;
    switch (formula.operator) {
    case '∧': {
        con = [this.cnf(formula.sub1), this.cnf(formula.sub2)];
        break;
    }
    case '∨': {
        dis = [this.cnf(formula.sub1), this.cnf(formula.sub2)];
        break;
    }
    case '→': {
        dis = [this.cnf(formula.sub1.negate()), this.cnf(formula.sub2)];
        break;
    }
    case '↔' : {
        con1 = this.cnf(new BinaryFormula('→', formula.sub1, formula.sub2));
        con2 = this.cnf(new BinaryFormula('→', formula.sub2, formula.sub1));
        con = [con1, con2];
        break;
    }
    case '¬' : {
        var sub = formula.sub;
        switch (sub.operator) {
        case '∧': {
            dis = [this.cnf(sub.sub1.negate()), this.cnf(sub.sub2.negate())];
            break;
        }
        case '∨': {
            con = [this.cnf(sub.sub1.negate()), this.cnf(sub.sub2.negate())];
            break;
        }
        case '→': {
            con = [this.cnf(sub.sub1), this.cnf(sub.sub2.negate())];
            break;
        }
        case '↔' : {
            // dis1 = this.cnf(new BinaryFormula('∧', sub.sub1, sub.sub2.negate()));
            // dis2 = this.cnf(new BinaryFormula('∧', sub.sub1.negate(), sub.sub2));
            // dis = [dis1, dis2];
            con1 = this.cnf(new BinaryFormula('∨', sub.sub1, sub.sub2));
            con2 = this.cnf(new BinaryFormula('∨', sub.sub1.negate(), sub.sub2.negate()));
            con = [con1, con2];
            break;
        }
        case '¬' : {
            return this.cnf(sub.sub);
        }
        }
    }
    }
    var res = [];
    if (con) {
        // con1 is [C1, C2 ...], con2 is [D1, D2, ...], where the elements are
        // clauses; return [C1, C2, ..., D1, D2, ...]:
        res = con[0].concatNoDuplicates(con[1]);
    }
    else if (dis) {
        // dis1 is [C1, C2 ...], dis2 is [D1, D2, ...], where the elements are
        // disjunctions of literals; (C1 & C2 & ...) v (D1 & D2 & ..) is
        // equivalent to (C1 v D1) & (C1 v D2) & ... (C2 v D1) & (C2 V D2) &
        // ...; so return [C1+D1, C1+D2, ..., C2+D1, C2+D2, ...]:
        for (var i=0; i<dis[0].length; i++) {
            for (var j=0; j<dis[1].length; j++) {
                // dis[0][i] and dis[1][j] are clauses, we want to combine them
                // log('adding '+dis[0][i].concat(dis[1][j]));
                res.push(dis[0][i].concatNoDuplicates(dis[1][j]).sort());
                // (sort each clause so that we can remove duplicate clauses)
            }
        }
    }
    res.sort(function(a,b){ return a.length - b.length });
    return res;
}

ModelFinder.prototype.simplifyClauses = function(clauseList) {
    /**
     * simplify <clauseList>
     */

    // remove clauses that contain contradictory formulas, e.g. [p,q,¬p]:
    var nl = clauseList.filter(function(clause) {
        for (var i=0; i<clause.length; i++) {
            for (var j=i+1; j<clause.length; j++) {
                if (clause[i].sub && clause[i].sub.string == clause[j].string ||
                    clause[j].sub && clause[j].sub.string == clause[i].string) {
                    return false;
                }
            }
        }
        return true;
    });

    // TODO: if an atom occurs only positively/negatively in the list of
    // clauses, it can be set as true/false;

    // // remove repetitions in clauses, as in [p,p,q]:
    // var nl = nl.map(function(clause) {
    //     return clause.removeDuplicates();
    // });

    // If clause A is a subset of (or equal to) clause B, clause B can be
    // removed (e.g. [[p],[p,q]] => [[p]] or [[q,s],[p,q,r,s]] => [[q,s]]. The
    // naive way to test this is O(n!). The following still takes too long if we
    // have a lot of clauses.
    nl2 = nl.copy();
    // We store which clauses contain which literals: q => [c1,c2],...
    var literals2clauses = {};
    for (var i=0; i<nl.length; i++) {
        for (var k=0; k<nl[i].length; k++) {
            var lit = nl[i][k].string;
            if (!literals2clauses[lit]) literals2clauses[lit] = [nl[i]];
            else literals2clauses[lit].push(nl[i]);
        }
    }
    // We look for supersets of each clause:
    for (var i=0; i<nl.length; i++) {
        var clause = nl[i];
        var lit = clause[0].string;
        var supersets = literals2clauses[lit];
        // log(clause+': supsersets from first literal: '+supersets);
        for (var k=1; k<clause.length && supersets.length; k++) {
            lit = clause[k].string;
            supersets.intersect(literals2clauses[lit]);
            // log(clause+': supsersets from next literal: '+supersets);
        }
        // log(clause+' is contained in '+supersets);
        for (var k=0; k<supersets.length; k++) {
            if (nl.indexOf(supersets[k]) > nl.indexOf(clause)) {
                nl2.remove(supersets[k]);
            }
        }
    }
    return nl2;
}

ModelFinder.prototype.nextStep = function() {
    /**
     * Each call of this function tries to extend the interpretation function of
     * this.model so that it satisfies the first literal in the first clause
     * from this.model.clauses. If we fail, we remove the literal from the
     * clause. If we succeed, we remove the entire clause and simplify the
     * remaining clauses.
     */

    log("** modelfinder: "+this.model.clauses);
    log("D: "+this.model.domain+"/"+this.model.worlds);
    log(dictToString(this.model.curInt));
    if (this.model.clauses.length == 0) {
        log('done');
        return true;
    }
    var literal = this.model.clauses[0][0];
    if (!literal) {
        // If the first clause contains no more literals, it can't be satisfied; we
        // need to backtrack:
        this.backtrack();
        return false;
    }
    while (this.model.clauses[0].length == 1 && literal.string.indexOf('$') > -1) {
        // We ultimately don't care about the interpretation of tseitin
        // formulas, and if they occur in a unit clause, we have no choice of
        // how to interpret them.
        log('applying unit resolution to '+literal);
        this.model.unitResolve(literal);
        return false;
    }

    log("trying to satisfy "+literal);

    // If we're processing this literal for the first time, we need to set up a
    // tentative interpretation of its terms and subterms. If we've backtracked
    // to this literal, we instead change its tentative interpretation to the
    // next possible interpretation.
    if (!this.model.termValues) {
        // NB: model.termValues stores only the values for the current literal
        this.model.initTermValues(literal);
    }
    else {
        if (!this.model.iterateTermValues()) {
            log("no more term interpretations to try: giving up");
            // try next disjunct in first clause on next attempt:
            this.model.clauses[0].shift();
            this.model.termValues = null;
            return false;
        }
    }
    
    while (true) {
        // check if the literal is true, or can be made true by extending the
        // predicate interpretation:
        var atom = literal.sub || literal;
        // NB: (atom == literal) is the truth-value we want for atom.

        // look up predicate for interpreted term values in curInt:
        var nterms = this.model.reduceTerms(atom.terms);
        var redAtom = atom.predicate+nterms.toString();
        if (this.model.getCurInt(redAtom) === (atom != literal)) {
            // failure: literal is false; try with a different term
            // interpretation:
            log("literal is false on present term interpretation");
            if (!this.model.iterateTermValues()) {
                log("no more term interpretations to try: giving up");
                this.model.clauses[0].shift();
                this.model.termValues = null;
                return false;
            }
        }
        else {
            // success! store present state for backtracking, then extend
            // model.interpretation by the tentative interpretation:
            this.alternativeModels.push(this.model.copy());
            if (this.model.getCurInt(redAtom) === undefined) {
                // predicate is undefined for terms; extend its interpretation:
                log('setting value for '+redAtom+' to '+(atom==literal));
                this.model.curInt[redAtom] = (atom==literal);
            }
            log("literal is satisfied: "+redAtom+" -> "+this.model.getCurInt(redAtom));
            this.model.interpretation = this.model.curInt;
            this.model.termValues = null;
            this.model.clauses.shift();
            this.model.simplifyRemainingClauses();
            return false;
        }
    }
}

ModelFinder.prototype.backtrack = function() {
    /**
     * try a different interpretation
     */
    log("backtracking");
    if (this.alternativeModels.length == 0) {
        log("no more models to backtrack; initializing larger model");
        var numWorlds = this.model.worlds.length;
        var numIndividuals = this.model.domain.length;
        if (numWorlds && this.parser.isPropositional) {
            numWorlds++;
        }
        else {
            if (numWorlds && numWorlds < this.model.domain.length) {
                numWorlds++;
            }
            else numIndividuals++; 
        }
        this.model = new Model(this, numIndividuals, numWorlds);
    }
    else {
        this.model = this.alternativeModels.pop();
        // recover this.model.curInt:
        this.model.curInt = {};
        for (var p in this.model.interpretation) {
            this.model.curInt[p] = this.model.interpretation[p];
        }
        var tvs = this.model.termValues;
        for (var i=0; i<tvs.length; i++) {
            var redTerm = this.model.reduceArguments(tvs[i][0]).toString();
            if (tvs[i][2] !== null) {
                this.model.curInt[redTerm] = tvs[i][2];
            }
        }
    }
}

function Model(modelfinder, numIndividuals, numWorlds) {
    /**
     * A (partial) model; also serves as a modelfinder state for backtracking
     */

    if (!modelfinder) { // called from copy()
        return;
    }
    
    this.modelfinder = modelfinder;
    this.parser = modelfinder.parser;

    // initialize domains:
    this.domain = Array.getArrayOfNumbers(numIndividuals);
    this.worlds = Array.getArrayOfNumbers(numWorlds);
    this.isModal = numWorlds > 0;
    log('model domain '+this.domain+', worlds '+this.worlds);

    // initialize interpretation function:
    this.interpretation = {}; // e.g. 'a' => 0, '[f,0]' => 2, 'F[0]' => true

    // initialize clauses we need to satisfy:
    this.clauses = this.getDomainClauses();
    log(this.clauses.length+" clauses");

    // list of all terms that we need to interpret; e.g. 'a','f(0)','f(1)':
    var terms = this.getTerms();
    this.indivTerms = terms[0];
    this.worldTerms = terms[1];
    
    // tentative interpretation of terms in current literal:
    this.termValues = null;

    // tentative combined interpretation:
    this.curInt = {};
}

Model.prototype.getTerms = function() {
    /**
     * return all terms that need to be interpreted in the model as strings
     * sorted by length; returns one list for individual terms and one for world
     * terms; includes skolem terms, but with nested terms reduced; i.e. on
     * domain { 0,1 }, term f(f(a)) is represented by terms a, f(0), f(1).
     */
    var indivTerms = [];
    var worldTerms = this.parser.isModal ? [this.parser.w] : [];
    for (var i=0; i<this.parser.symbols.length; i++) {
        var s = this.parser.symbols[i];
        var stype = this.parser.expressionType[s];
        if (stype == 'individual constant') {
            indivTerms.push(s);
        }
        else if (stype.indexOf('function symbol for world') > -1) {
            var arity = this.parser.arities[s];
            Model.getNTuples(arity, this.worlds.length-1).forEach(function(li) {
                li.unshift(s);
                worldTerms.push(li.toString());
            });
        }
        else if (stype.indexOf('function symbol') > -1) {
            var arity = this.parser.arities[s];
            Model.getNTuples(arity, this.domain.length-1).forEach(function(li) {
                li.unshift(s);
                indivTerms.push(li.toString());
            });
        }
    }
    indivTerms.sort(function(a,b){ return a.length - b.length; });
    worldTerms.sort(function(a,b){ return a.length - b.length; });
    return [indivTerms, worldTerms];
}

Model.prototype.getDomainClauses = function() {
    /**
     * turn modelfinder.clauses into a variable-free list of clauses that serves
     * as constraints on interpretations. If the domain is [0,1], then a clause
     * ['Fx','xRy'] is turned into ['F0','0R0'], ['F0','0R1'], ['F1','1R0'],
     * ['F1','1R1'].
     */
    res = [];
    log('creating clauses for current domain(s)');
    for (var c=0; c<this.modelfinder.clauses.length; c++) {
        var clause = this.modelfinder.clauses[c];
        // log('  clause '+clause);
        // collect all variables in the clause:
        var variables = [];
        for (var i=0; i<clause.length; i++) {
            variables.extendNoDuplicates(this.parser.getVariables(clause[i])); // optimise
        }
        if (variables.length == 0) {
            // log('    adding clause to constraint');
            res.push(clause.copy());
            continue;
        }
        // get all possible interpretations of the variables:
        var interpretations = this.getVariableAssignments(variables);
        // log('    variables: '+variables+', interpretations: '+interpretations);
        // e.g. [[0,0],[0,1],[1,0],[1,1]] for two variables and domain [0,1]
        for (var i=0; i<interpretations.length; i++) {
            var interpretation = interpretations[i];
            // log('    adding clause for interpretation '+interpretation);
            var nclause = clause.map(function(formula) {
                var nformula = formula;
                for (var i=0; i<variables.length; i++) {
                    nformula = nformula.substitute(variables[i], interpretation[i]);
                }
                return nformula;
            });
            res.push(nclause);
        }
    }

    log('           clauses: '+res);
    res = this.modelfinder.simplifyClauses(res);
    log('simplified clauses: '+res);
    return res;
}

Model.prototype.getVariableAssignments = function(variables) {
    /**
     * list all interpretations of <variables> on the model's domain(s), as
     * sequences; e.g. [[0,0],[0,1],[1,0],[1,1]] for domain=[0,1] and two
     * individual variables.
     */
    var res = [];
    var tuple = Array.getArrayOfZeroes(variables.length);
    res.push(tuple.copy());
    var maxValues = [];
    for (var i=0; i<variables.length; i++) {
        maxValues.push(this.parser.expressionType[variables[i]] == 'variable' ?
                       this.domain.length-1 : this.worlds.length-1);
    }
    while (Model.iterateTuple(tuple, maxValues)) { // optimise?
        res.push(tuple.copy());
    }
    return res;
}

Model.iterateTuple = function(tuple, maxValues) {
    /**
     * changes tuple to the next tuple in the list of all tuples of the same
     * length whose i-the element is one of {0..maxValues[i]}
     */
    for (var i=tuple.length-1; i>=0; i--) {
        if (tuple[i] < maxValues[i]) {
            tuple[i]++;
            return true;
        }
        tuple[i] = 0;
    }
    return false;
    // Example 1: tuple = 011, all maxValues 2.
    //   at i=2, tuple -> 012, return true
    // Example 2: tuple = 011, maxValues 1.
    //   at i=2, tuple -> 010
    //   at i=1, tuple -> 000
    //   at i=0, tuple -> 100, return true
}

Model.getNTuples = function(n, maxval) {
    /**
     * return all <n>-tuples of numbers up to <maxval>
     *
     * E.g., for n=2 and maxval=1 return [[0,0],[0,1],[1,0],[1,1]].
     */
    if (n == 0) {
        return [[]];
    }
    var res = [];
    for (var i=0; i<maxval; i++) {
        Model.getNTuples(n-1, maxval).forEach(function(li) {
            li.unshift(i);
            res.push(li);
        });
    }
    return res;
}


Model.prototype.initTermValues = function(literal) {
    /**
     * this.termValues is a list of triples, one for each non-numerical term
     * and subterm from <literal>, in order of increasing complexity. The
     * triple elements are:
     *    
     * [0]: the term itself,
     * [1]: the term as string,
     * [2]: the term's current tentative value, or null if the value is
     *      determined by this.interpretation together with items earlier in the
     *      list.
     * 
     * We have to make sure we're interpreting function terms consistently, so
     * that we don't end up with inconsistent interpretations like these:
     *    
     * - |a|=0, |f(0)|=1, |f(a)|=0
     * - |f(a)|=0, |f(0)|=1, |f(f(a))|=0
     * - |a|=0, |f(a)|=0, |f(f(0))|=1.
     * - |f(a)|=0, |f(f(a))|=1, |f(b)|=1, |b|=1, D = {0,1}
     *
     * Whenever we interpret a nested term like f(f(a)), we first interpret its
     * smallest non-numerical subterms. (These subterms will not have an old
     * interpretation, otherwise they would have been replaced by their
     * numerical values.) So when we try to satisfy Af(f(a)), and a doesn't have
     * a current value, we interpret a as 0. The next term to interpret is then
     * f(a), which reduces to f(0). We check if this has an (old or current)
     * interpretation. If not, we interpret it as 0. And so on.
     *    
     * If the initial interpretation didn't work out, we need to try others.
     * (This isn't trivial because we don't have a fixed set of terms to
     * interpret in any given disjunct: if a disjunct contains f(a), and f(0) is
     * previously defined but f(1) is not, then setting |a|=1 requires also
     * setting |f(1)|, but setting |a|=0 does not require setting anything
     * else.)
     *    
     * Here's what we do:
     * 
     * 1. We make a list of all non-numerical subterms in the term list, in
     *    order of complexity. E.g.: [a,b,g(0,0),f(b),g(a,0),f(f(b))]
     *      
     * 2. For each term in the list (LTR), we check if its extension is
     *    determined by the current interpretation. If yes, we pair it with the
     *    value null. If no, we pair it with a new value 0. 
     *        
     *    E.g.: if the old interpretation has f(0)=0, the above ex. turns into 
     *    [(a,0),(b,0),(g(0,0),0),(f(b),null),(g(a,0),null),(f(f(b)),null)]
     *    - f(b) is null because b is 0 and f(0) is fixed
     *    - g(a,0) is null because a is 0 and we've set g(0,0) 
     *    - f(f(b)) is null because f(b)=f(0) is 0 and f(0) is fixed
     *    
     * 3. When iterating, we go through the list of pairs RTL, trying to
     *    increase a value:
     *    - If the term has null value, we skip it.
     *    - If the term has its max value, we reset it to 0.
     *    - If the term has a value less than its max value, we increase it. 
     *      We then recompute the values of the terms to the right of the
     *      present term and exit the loop.
     */
    log("initializing termValues in "+literal);
    
    var atom = literal.sub || literal;
    var termIsOld = {};
    var terms = [];
    
    // We first add each original term with its string value.
    for (var i=0; i<atom.terms.length; i++) {
        if (typeof atom.terms[i] == 'number') continue;
        var termStr = atom.terms[i].toString();
        if (termIsOld[termStr]) continue;
        termIsOld[termStr] = true;
        terms.push([atom.terms[i], termStr, null]);
    }

    // Next we add the subterms:
    for (var i=0; i<terms.length; i++) {
        if (terms[i][0].isArray) {
            for (var j=1; j<terms[i][0].length; j++) {
                var subTerm = terms[i][0][j];
                if (typeof subTerm == 'number') continue;
                var termStr = subTerm.toString();
                if (termIsOld[termStr]) continue;
                termIsOld[termStr] = true;
                terms.push([subTerm, termStr, null]);
            }
        }
    }

    // sort term list by length, to ensure that a term is never a subterm of any
    // term to its left:
    terms.sort(function(a,b){
        return a[1].length - b[1].length;
    });

    // tentatively interpret all terms and subterms:
    this.curInt = {};
    for (var p in this.interpretation) {
        this.curInt[p] = this.interpretation[p];
    }
    for (var i=0; i<terms.length; i++) {
        var redTerm = this.reduceArguments(terms[i][0]).toString();
        if (!(redTerm in this.curInt)) {
            terms[i][2] = 0;
            this.curInt[redTerm] = 0;
        }
    }

    this.termValues = terms;
    log(this.termValues.toString());
}

Model.prototype.isWorldTerm = function(term) {
    /**
     * return true iff <term> is a term that denotes a world
     */
    if (!this.parser.isModal) {
        return false;
    }
    if (term.isArray) {
        return this.isWorldTerm(term[0]);
    }
    return (this.parser.expressionType[term].indexOf("world") > -1);
}

Model.prototype.getMaxValue = function(term, termStr) {
    /**
     * return the maximum value that can be assigned to <term>
     * 
     * We want to avoid redundant permutations. There's no point trying |a|=0,
     * |b|=1 and later |a|=1, |b|=0. So we fix the first constant to always
     * denote 0. The second either denotes 0 or (if available) 1, but never 2.
     * And so on. The function term f(0) is allowed to denote 1, even if no term
     * yet denotes 0.
     */
    var isWorldTerm = this.isWorldTerm(term);
    var domain = isWorldTerm ? this.worlds : this.domain;
    var termList = isWorldTerm ? this.worldTerms : this.indivTerms;
    var maxValue = domain.length - 1; 
    var index = termList.indexOf(termStr);
    if (index > -1 && index < maxValue) {
        // maxValue is index, unless term has larger elements as arguments
        maxValue = index;
        if (term.isArray) {
            // termList only contains fully reduced terms, so we don't need to
            // worry about nested function expressions.
            for (var i=1; i<term.length; i++) {
                if (term[i] >= maxValue) {
                    maxValue = term[i] + 1;
                }
            }
        }
    }
    log("maxValue "+maxValue);
    return maxValue;
}

Model.prototype.reduceArguments = function(term) {
    /**
     * replace arguments in <term> (or in subterms of <term>) by their numerical
     * values, as per this.curInt.
     */
    if (term.isArray) {
        var nterm = this.reduceTerms(term, 1);
        nterm.unshift(term[0]);
        return nterm;
    }
    return term;
}

Model.prototype.reduceTerms = function(terms, startIndex) {
    /**
     * replace each term and subterm in <terms> by its numerical value, if it has
     * one in this.curInt. E.g., if curInt['a']=0, and '[f,a]' and 'b' are not in
     * curInt, then a => 0, b => b, [f,a] => [f,0].
     */
    var res = [];
    for (var i=(startIndex || 0); i<terms.length; i++) {
        if (typeof terms[i] == 'number') {
            res.push(terms[i]);
        }
        else if (terms[i].isArray) {
            var nterm = this.reduceTerms(terms[i], 1);
            nterm.unshift(terms[i][0]);
            var ntermStr = nterm.toString();
            if (ntermStr in this.curInt) {
                res.push(this.curInt[ntermStr]);
            }
            else {
                res.push(nterm);
            }
        }
        else {
            if (terms[i] in this.curInt) {
                res.push(this.curInt[terms[i]]);
            }
            else {
                res.push(terms[i]);
            }
        }
    }
    return res;
}

Model.prototype.iterateTermValues = function() {
    /**
     * try to minimally change the interpretation of the terms in the currently
     * processed literal (stored in this.termValues)
     *
     * Recall that this.termValues is a list of triples, one for each
     * non-numerical term and subterm in the literal, in order of increasing
     * complexity. The triple elements are:
     *    
     * [0]: the term itself,
     * [1]: the term as string,
     * [2]: the term's current tentative value, or null if the value is
     *      determined by this.interpretation together with items earlier in the
     *      list.
     */

    log("trying to iterate termValues");
    // Go through terms RTL:
    for (var i=this.termValues.length-1; i>=0; i--) {
        var tv = this.termValues[i];
        // skip uninterpreted terms:
        if (tv[2] === null) {
            continue;
        }
        var redTerm = this.reduceArguments(tv[0]);
        var redTermStr = redTerm.toString();
        var maxValue = this.getMaxValue(redTerm, redTermStr);
        if (tv[2] == maxValue) {
            // We can't increase the value of this term. We don't simply set it
            // to 0 because the change we make to an earlier term's
            // interpretation might fix the interpretation of this term. So we
            // set the interpretation to null for now and recompute it below.
            tv[2] = null;
            if (!this.interpretation[redTermStr]) {
                delete this.curInt[redTermStr];
            }
            continue;
        }
        tv[2]++;
        this.curInt[redTermStr] = tv[2];
        log('setting '+tv[1]+' (= '+redTermStr+') to '+tv[2]);
        
        // Now we recompute/reset the values of terms to the right. To this end,
        // we first have to fill back in the interpretation of reduced terms
        // that is implied by terms to the left:
        for (var j=0; j<i; j++) {
            if (this.termValues[j][2] !== null) {
                var rt = this.reduceArguments(this.termValues[j][0]).toString();
                this.curInt[rt] = this.termValues[j][2];
            }
        }
        for (var j=i+1; j<this.termValues.length; j++) {
            var rt = this.reduceArguments(this.termValues[j][0]).toString();
            if (this.curInt[rt] === undefined) {
                // interpretation not yet fixed
                this.termValues[j][2] = 0;
                this.curInt[rt] = 0;
            }
            else {
                this.termValues[j][2] = null;
            }
        }
        log(this.termValues.toString());
        if (this.isRedundant()) {
            // try another iteration; e.g. while a->0, b->0, c->2 is redundant
            // on D = {0,1,2}, the next iteration a->0, b->1, c->0 is not
            // redundant:
            return this.iterateTermValues();
        }
        return true;
    }
    return false;
}

Model.prototype.isRedundant = function(checkWorldTerms) {
    /**
     * check if the present interpretation of term values makes the model
     * isomorphic to a model we've already tried.
     *
     * We mostly avoid redundant models by setting a term's maxValue. But
     * sometimes a value less than maxValue can be skipped. For example, if we
     * have terms a,b,c and a and b both denote 0 then we don't need to try
     * |c|=1 and |c|=2.
     * 
     * The argument <checkWorldTerms> is for recursive calls only, because we
     * need to check world terms and individual terms separately.
     */

    var terms = checkWorldTerms ? this.worldTerms : this.indivTerms;
    var domain = checkWorldTerms ? this.worlds : this.domain;
    var unusedEls = domain.copy();

    for (var i=0; i<terms.length; i++) {
        var term = terms[i];
        // all argument terms count as used:
        if (term.indexOf('[') == 0) {
            var args = term.slice(1,-1).split(',');
            for (var j=1; j<args.length; j++) {
                unusedEls.remove(args[j]**1);
            }
            if (unusedEls.length == 0) break;
        }
        var val = this.curInt[term];
        if (!val || val == unusedEls[0]) {
            // If the term is uninterpreted, the interpretation may be
            // legitimately extended by assigning to the term the first unused
            // element in the domain.
            unusedEls.shift();
            if (unusedEls.length == 0) break;
        }
        if (val > unusedEls[0]) {
            log("interpretation should assign "+unusedEls[0]+" instead of "+val+" to "+term);
            return true;
        }
    }

    if (this.isModal && !checkWorldTerms) {
        return this.isRedundant(true);
    }
    return false;
}

Model.prototype.satisfy = function(literal) {
    /**
     * try to extend this.interpretation to satisfy <literal>; used in
     * sentree.js. (currently unused)
     */
    var atom = literal.sub || literal;
    this.curInt = this.interpretation;
    var nterms = this.reduceTerms(atom.terms);
    var redAtom = atom.predicate+nterms.toString();
    if (redAtom in this.curInt && thic.curInt[redAtom] != (atom==literal)) {
        return false;
    }
    this.interpretation[redAtom] = (atom==literal);
    return true;
}


Model.prototype.simplifyRemainingClauses = function() {
    /**
     * After a clause has been satisfied by extending the interpretion function,
     * we simplify the remaining clauses.
     *
     * (a) If we've assigned a value to new terms, we substitute all occurrences
     *     of these terms in later clauses by that value (e.g., turning Ac into
     *     A0).
     *
     * (b) We then remove any literals that are known to be false. (All these
     *     literals will be simple literals with numeral terms. If a literal
     *     doesn't have only numeral terms, it doesn't as yet have a
     *     truth-value.) We also remove entire clauses for which any literal is
     *     known to be true.
     *
     *     (E.g., if we've extended the predicate interpretation so as to make
     *     ~R00 true, then R00 is removed from any future clauses. Another
     *     example: We may have a past clause [A0], a future clause [~Ac,~Bc],
     *     and newly assign c -> 0. The future clause then turns into
     *     [~A0,~B0]. We simplify this to [~B0].)
     *
     * (c) Finally, we re-order the future clauses by number of literals.
     */

    log("simplifying remaining clauses:");
    log(this.clauses.toString());
    
    var nclauses = [];
    CLAUSELOOP:
    for (var i=0; i<this.clauses.length; i++) {
        var nclause = [];
        for (var j=0; j<this.clauses[i].length; j++) {
            var literal = this.clauses[i][j];
            var atom = literal.sub || literal;
            // look up predicate for interpreted term values in curInt:
            var nterms = this.reduceTerms(atom.terms);
            var redAtomStr = atom.predicate+nterms.toString();
            if (redAtomStr in this.curInt) {
                if (this.curInt[redAtomStr] == (atom==literal)) {
                    // literal is true; skip clause
                    continue CLAUSELOOP;
                }
                else { 
                    // literal is false; skip literal
                    continue;
                }
            }
            if (atom.terms.toString() != nterms.toString()) {
                // replace literal by interpreted literal:
                var redAtom = new AtomicFormula(atom.predicate, nterms);
                var nlit = atom == literal ? redAtom : new NegatedFormula(redAtom);
                nclause.push(nlit);
            }
            else nclause.push(literal);
        }
        nclauses.push(nclause);
    }
    nclauses.sort(function(a,b) {
        // process unit clauses with tseitin formulas first:
        if (a.length == 1 && b.length == 1) {
            return b[0].string.indexOf('$') - a[0].string.indexOf('$');
        }
        return a.length - b.length;
    });
    log(nclauses.toString());
    this.clauses = nclauses;
}

Model.prototype.unitResolve = function(literal) {
    /**
     * <literal> is a tseitin formula in a unit clause; we can interpret it as true
     * and simplify the remaining clauses accordingly.
     */
    var negLiteralString = (literal.sub && literal.sub.string) || '¬'+literal.string;
    var nclauses = [];
    CLAUSELOOP:
    for (var i=1; i<this.clauses.length; i++) {
        var nclause = [];
        for (var j=0; j<this.clauses[i].length; j++) {
            if (this.clauses[i][j].string == literal.string) {
                continue CLAUSELOOP;
            }
            if (this.clauses[i][j].string != negLiteralString) {
                nclause.push(this.clauses[i][j]);
            }
        }
        nclauses.push(nclause);
    }
    nclauses.sort(function(a,b) {
        // process unit clauses with tseitin formulas first:
        if (a.length == 1 && b.length == 1) {
            return b[0].string.indexOf('$') - a[0].string.indexOf('$');
        }
        return a.length - b.length;
    });
    this.clauses = nclauses;
}

Model.prototype.getCurInt = function(redAtom) {
    /**
     * return this.curInt[<redAtom>], except if <redAtom> is an identity
     * formula, in which case the interpretation is settled
     */
    if (redAtom[0] == '=') {
        // redAtom is a string like '=[0,1]'
        var terms = redAtom.slice(2,-1).split(',');
        if (!isNaN(terms[0]) && !isNaN(terms[1])) {
            return terms[0] == terms[1];
        }
    }
    return this.curInt[redAtom];
}

Model.prototype.copy = function() {
    /**
     * return a shallow copy of the model, for backtracking.
     */
    var nmodel = new Model();
    nmodel.modelfinder = this.modelfinder;
    nmodel.parser = this.parser;
    nmodel.domain = this.domain;
    nmodel.worlds = this.worlds;
    nmodel.isModal = this.isModal;
    nmodel.interpretation = this.interpretation;
    nmodel.termValues = this.termValues;
    nmodel.clauses = this.clauses.copyDeep();
    nmodel.indivTerms = this.indivTerms;
    nmodel.worldTerms = this.worldTerms;
    // curInt isn't copied (contains later predicate interpretations)
    return nmodel;
}

Model.prototype.toHTML = function() {
    /**
     * return HTML representation of the model to display as countermodel
     */
    var str = "<table>";
    if (this.parser.isModal) {
        // change world names from '0', '1', .. to 'w0', 'w1', ..:
        function w(num) {
            return 'w<sub>'+num+'</sub>';
        }
        str += "<tr><td align='right'>Worlds: </td><td align='left'>{ ";
        str += this.worlds.map(function(n){return w(n)}).join(", ");
        str += " }</td></tr>\n";
        if (!this.parser.isPropositional) {
            str += "<tr><td align='right'>Individuals: </td><td align='left'>{ ";
            str += this.domain.join(", ");
            str += " }</td></tr>\n";
        }
    }
    else if (!this.parser.isPropositional) {
        str += "<tr><td align='right'>Domain: </td><td align='left'>{ ";
        str += this.domain.join(", ");
        str += " }</td></tr>\n";
    }

    // display constants and function symbols:
    // a: 0
    // f: { <0,1>, <1,1> }
    
    var extensions = this.getExtensions();

    for (var i=0; i<this.modelfinder.constants.length; i++) {
        var sym = this.modelfinder.constants[i];
        var ext = extensions[sym];
        var val = sym == this.parser.w ? w(ext) : ext;
        if (sym == this.parser.w) sym = '@';
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    
    for (var i=0; i<this.modelfinder.funcSymbols.length; i++) {
        var sym = this.modelfinder.funcSymbols[i];
        var ext = extensions[sym];
        // ext is something like [1,2] or [[0,1],[1,1]]
        if (ext.length > 0 && !ext[0].isArray) {
            // extensions[sym] is something like [1,2]
            var val = '{ '+ext.join(',')+' }';
        }
        else {
            // extensions[sym] is something like [[0,1],[1,1]]
            var val = '{ '+ext.map(function(tuple) {
                return '('+tuple.join(',')+')';
            }).join(', ')+' }';
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    
    // display predicates and proposition letters:
    // p: true/1
    // F: { 0,1 }
    // G: { <0,0>, <1,1> }

    var isModal = this.parser.isModal;
    var R = this.parser.R;
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        var sym = this.modelfinder.predicates[i];
        if (sym == '=') continue;
        var ext = extensions[sym];
        var val;
        if (!ext.isArray) { // zero-ary
            val = ext;
        }
        else if (ext.length > 0 && !ext[0].isArray) {
            // ext is something like [1,2]
            if (isModal) ext = ext.map(function(n){return w(n)});
            val = '{ '+ext.join(',')+' }';
        }
        else {
            // ext is something like [[0,1],[1,1]]
            val = '{ '+ext.map(function(tuple) {
                if (isModal) {
                    tuple[tuple.length-1] = w(tuple[tuple.length-1]);
                    if (sym == R) tuple[0] = w(tuple[0]);
                }
                return '('+tuple.join(',')+')';
            }).join(', ')+' }';
        }
        if (sym == R && sym != 'R') {
            // 'R' is used as predicate, our internal accessibility symbol won't mean much to the user
            sym = 'Accessibility'
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }

    str += "</table>";
    return str;
}

Model.prototype.getExtensions = function() {
    /**
     * this.interpretation is a dict with entries like 'a' => 0, '[f,0]' => 0,
     * '[p]' => true, '[R,0,1]' => false.  We return a new dict that assigns
     * extensions to all non-logical expressions in initFormulas, with records
     * like 'f' => [(0,0),(1,0)], 'R' => [(0,1)].
     */
    var result = {};
    // constants:
    for (var i=0; i<this.modelfinder.constants.length; i++) {
        var cons = this.modelfinder.constants[i];
        result[cons] = this.interpretation[cons] || 0;
    }
    var interpretedStrings = Object.keys(this.interpretation);
    // function symbols:
    for (var i=0; i<this.modelfinder.funcSymbols.length; i++) {
        var f = this.modelfinder.funcSymbols[i];
        result[f] = [];
        for (var j=0; j<interpretedStrings.length; j++) {
            var expr = interpretedStrings[j];
            if (expr.indexOf('['+f+',') == 0) { // e.g. '[f,0]' 
                var args = expr.slice(1,-1).split(',');
                args.shift(); 
                var val = this.interpretation[expr];
                result[f].push(args.concat([val]));
            }
        }
        result[f] = this.makeFunctionExtensionTotal(f, result[f]);
    }
    // predicates:
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        var p = this.modelfinder.predicates[i];
        // Zero-ary predicates should have truth-values as extensions, one-ary
        // predicates list of individuals, other predicates lists of lists of
        // individuals.
        result[p] = (this.parser.arities[p] == 0) ? false : [];
        // NB: modal proposition letters have arity 1 
        for (var j=0; j<interpretedStrings.length; j++) {
            var expr = interpretedStrings[j];
            if (expr.indexOf(p+'[') == 0) { // e.g. 'F[0]'
                var val = this.interpretation[expr];
                var args = expr.substr(p.length).slice(1,-1).split(',');
                if (args[0] == '') { // sentence letter
                    result[p] = val;
                }
                else {
                    if (!val) continue; // only list positive extension
                    if (args.length == 1) {
                        result[p].push(args[0]);
                    }
                    else {
                        result[p].push(args);
                    }
                }
            }
        }
    }
    return result;
}

Model.prototype.makeFunctionExtensionTotal = function(f, extension) {
    /**
     * map all arguments for <f> that aren't covered in <extension> to 0
     */
    var arity = this.parser.arities[f];
    var args = Array.getArrayOfZeroes(arity);
    var maxValue = this.domain.length - 1;
    var maxValues = args.map(function(x){ return maxValue; });
    var res = [];
    ARGLOOP:
    do {
        for (var i=0; i<extension.length; i++) {
            if (extension[i].slice(0,-1).equals(args)) {
                res.push(extension[i]);
                continue ARGLOOP;
            }
        }
        res.push(args.concat([0]));
    } while (Model.iterateTuple(args, maxValues));
    return res;
}

Model.prototype.toString = function() {
    /**
     * return string representation of model, for debugging
     */
    return this.toHTML().replace(/<.+?>/g, '');
}

function dictToString(dict) {
    /**
     * return string representation of associative array, for debugging
     */
    var res = '';
    var keys = Object.keys(dict);
    for (var i=0; i<keys.length; i++) {
        res += keys[i]+': '+dict[keys[i]]+'\n';
    }
    return res;
}
