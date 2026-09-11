
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
 *    numerals. So for domain { 0,1 }, [Ff(x)] would be replaced by two clauses,
 *    [Ff(0)] and [Ff(1)].
 *    
 * 4. We now iterate over all possible interpretations of the predicates and
 *    function expressions. For each expression, we first record the clauses
 *    that contain it. Then we enter this loop:
 *
 *    a. Take the first/next uninterpreted expression.
 *    b. For each possible interpretation of that expression:
 *       i. Substitute that interpretation into the clauses.
 *       ii. Simplify the new clauses.
 *       iii. If the new clauses contain an empty clause, the interpretation
 *            is not a model; try the next.
 *       iii. If the new clauses force the interpretation of any other
 *            expression, update the interpretation and repeat from i.
 *    c. If no interpretation of the expression worked, backtrack.
 *            
 * Models for originally modal formulas (which we recognize from parser.isModal)
 * have two domains, W and D. The elements of W are also natural numbers
 * starting with 0. Accessibility conditions like reflexivity are added to the
 * formulas for which we want to find a model. In modal models, all predicates
 * take a world as their last argument; 'R' takes two worlds, function terms
 * only take individuals.
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
    
    // Rename numeric constants (e.g. "0") to avoid collision with domain elements.
    this.numericConstRestore = {};
    for (var i=0; i<this.constants.length; i++) {
        if (/^\d+$/.test(this.constants[i])) {
            var orig = this.constants[i];
            var renamed = 'ν'+orig;
            this.numericConstRestore[renamed] = orig;
            this.constants[i] = renamed;
            parser.registerExpression(renamed, 'individual constant', 0);
            initFormulas = initFormulas.map(f => f.substitute(orig, renamed));
        }
    }

    // break down initFormulas and accessibilityConstraints into clauses:
    initFormulas = initFormulas.concat(accessibilityConstraints || []);
    this.clauses = this.getClauses(initFormulas);
    
    // initialize model:
    var numIndividuals = 1;
    var numWorlds = this.parser.isModal ? 1 : 0;
    this.model = new Model(this, numIndividuals, numWorlds);

    // cell-based search state, see below:
    this.searchStack = [];
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
     *
     * A tseitin-type "definitional" transformation is used if it reduces the
     * number of clauses without introducing too many variables.
     */
    var resNormal = []; // clauses computed by ordinary cnf transformation
    // var resTseitin = []; // clauses computed with tseitin transformation
    var resDefinitional = []; // clauses computed with definitional transformation
    const MAX_CLAUSES = 100000; // if cnf has more, use definitional transformation
    var usingTseitin = false;
    for (var i=0; i<formulas.length; i++) {
        var formula = formulas[i];
        log('getting clauses from '+formula);
        var distinctVars = this.makeVariablesDistinct(formula);
        log('distinctVars: '+distinctVars);
        var skolemized = this.skolemize(distinctVars);
        log('skolemized: '+skolemized);
        var clausesDefinitional = this.definitionalCNF(skolemized);
        log('definitional cnf: '+clausesDefinitional);
        resDefinitional.extendNoDuplicates(clausesDefinitional);
        var quantifiersRemoved = skolemized.removeQuantifiers();
        log('qantifiers removed: '+quantifiersRemoved);
        try {
            var clauses = this.cnf(quantifiersRemoved, MAX_CLAUSES);
            resNormal.extendNoDuplicates(clauses);
            log('cnf: '+clauses);
        } catch(e) {
            if (e.message !== "CNF_TOO_BIG") throw e;
            log('CNF too big, using definitional transformation for this formula');
            resNormal.extendNoDuplicates(clausesDefinitional);
            usingTseitin = true;
        }
    }
    resNormal = this.simplifyClauses(resNormal);
    resDefinitional = this.simplifyClauses(resDefinitional);
    resDefinitional = this.eliminateUniversalTseitinPredicates(resDefinitional);
    log('combined standard clauses: '+resNormal);
    log('combined definitional clauses: '+resDefinitional);

    // Estimate which set of clauses is likely to be faster to ground and search:
    var parser = this.parser;
    function groundingCost(clauses) {
        // estimate grounding cost at domain size 2: sum of 2^(num_vars) per clause.
        var cost = 0;
        for (var i=0; i<clauses.length; i++) {
            var vars = [];
            for (var j=0; j<clauses[i].length; j++) {
                vars.extendNoDuplicates(parser.getVariables(clauses[i][j]));
            }
            cost += Math.pow(2, vars.length);
            if (!isFinite(cost)) return Infinity;
        }
        return cost;
    }
    function newCells(clauses) {
        // count the cells the new predicates in <clauses> will need.
        var predicates = new Set();
        for (var i=0; i<clauses.length; i++) {
            for (var j=0; j<clauses[i].length; j++) {
                var lit = clauses[i][j];
                var pred = (lit.sub || lit).predicate;
                if (parser.expressionType[pred] === 'tseitin predicate') {
                    predicates.add(pred);
                }
            }
        }
        var cells = 0;
        predicates.forEach(function(pred) { cells += Math.pow(2, parser.arities[pred]) });
        return cells;
    }
    var costPlain = groundingCost(resNormal);
    var costDefinitional = groundingCost(resDefinitional);
    var extraCells = newCells(resDefinitional) - newCells(resNormal);
    log('grounding cost (plain): '+costPlain+', (definitional): '+costDefinitional+' with '+extraCells+' extra cells');
    var chosen;
    if (costDefinitional * (1 + Math.max(0, extraCells)) < costPlain) {
        log('using combined definitional cnf');
        chosen = resDefinitional;
    }
    else {
        log('using combined standard cnf');
        chosen = resNormal;
        if (usingTseitin) {
            chosen = this.eliminateUniversalTseitinPredicates(chosen);
        }
    }
    
    // Remove from the parser every tseitin predicate that no longer appears in
    // any chosen clause:
    var used = new Set();
    for (var i=0; i<chosen.length; i++) {
        for (var j=0; j<chosen[i].length; j++) {
            var lit = chosen[i][j];
            used.add((lit.sub || lit).predicate);
        }
    }
    this.parser.symbols = this.parser.symbols.filter(function(s) {
        if (this.parser.expressionType[s] === 'tseitin predicate' && !used.has(s)) {
            delete this.parser.expressionType[s];
            delete this.parser.arities[s];
            delete this.parser.predicateArgTypes[s];
            return false;
        }
        return true;
    }.bind(this));

    return chosen;
}

ModelFinder.prototype.makeVariablesDistinct = function(formula) {
    /**
     * Return an equivalent variant of <formula> that doesn't reuse the same
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
     * Return <formula> with existential quantifiers skolemized away.
     */
    log('skolemizing '+formula);
    var boundVars = arguments[1] ? arguments[1].copy() : [];
    // log(formula.string+' bv: '+boundVars);
    var parser = this.parser;
    if (formula.quantifier == '∃') {
        // skolemize on variables that are bound at this point and that occur in
        // the matrix (ignoring formula.variable)
        var skolemVars = [];
        var matrixVars = parser.getVariables(formula.matrix);
        boundVars.forEach(function(v) {
            if (matrixVars.includes(v)) skolemVars.push(v);
        });
        var isWorldType = parser.expressionType[formula.variable] == 'world variable';
        var skolemTerm;
        if (skolemVars.length > 0) {
            var funcSymbol = parser.getNewFunctionSymbol(skolemVars.length, isWorldType);
            parser.functionArgTypes[funcSymbol] = skolemVars.map(function(v) {
                return parser.expressionType[v];
            });
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

ModelFinder.prototype.cnf = function(formula, maxClauses = Infinity) {
    /**
     * Convert <formula> (in NNF) to CNF.
     *
     * This can easily blow up and crash the browser, e.g. for
     * ∀y(m=y↔(∀x(Lxy↔Fx)∧(y=e∨∃zLzy))∨(y=e∧¬∃C∀x(LxC↔Fx)))↔∀y(m=y↔¬(∀x(Lxy↔Fx)∧∃zLzy)→((∀x(Lxy↔Fx)∧y=e)∨(y=e∧¬∃C∀x(LxC↔Fx))))
     * We throw an error if the CNF would have more than <maxClauses> clauses.
     */

    const cnfClauseKey = this.cnfClauseKey;
    const cnfNormalizeClause = this.cnfNormalizeClause;

    function cnfOr(dis1, dis2) {
        /**
         * Disjoin <dis1> and <dis2> for CNF computation.
         *
         * dis1 is [C1, C2 ...], dis2 is [D1, D2, ...], where the elements are
         * clauses, i.e. disjunctions of literals; (C1 & C2 & ...) v (D1 & D2 & ..)
         * is equivalent to (C1 v D1) & (C1 v D2) & ... (C2 v D1) & (C2 V D2) & ...;
         * so we should return [C1+D1, C1+D2, ..., C2+D1, C2+D2, ...], but we drop
         * duplicate clauses and tautologies (e.g. [p,¬p]). This can blow up.
         */
        const res = [];
        const seenClauses = new Set();

        if (dis1.length === 0 || dis2.length === 0) return [];
        if (dis1.length === 1 && dis1[0].length === 0) return dis2; // false v d2 = d2
        if (dis2.length === 1 && dis2[0].length === 0) return dis1; // d1 v false = d1                                                                

        if (dis1.length * dis2.length > maxClauses) {
            throw new Error("CNF_TOO_BIG");
        }

        for (const cl1 of dis1) {
            for (const cl2 of dis2) {
                const merged = cnfNormalizeClause(cl1.concat(cl2));
                if (merged === null) continue; // drop tautology clause
                const key = cnfClauseKey(merged);
                if (seenClauses.has(key)) continue; // duplicate clause
                seenClauses.add(key);
                res.push(merged);
            }
        }
        return res;
    }

    function toCNF(formula) {
        if (formula.type == 'literal') {
            // CNF with 1 clause containing the literal:
            return [[formula]];
        }
        if (formula.operator == '∨') {
            return cnfOr(toCNF(formula.sub1), toCNF(formula.sub2));
        }
        if (formula.operator == '∧') {
            // Conjoin the conjuncts of the (flattened) conjunction <formula>.
            // If the first conjunct has CNF [C1, C2 ...] and the second [D1, D2,
            // ...], where the elements are clauses, we collect [C1, C2, ..., D1,
            // D2, ...], dropping duplicates.
            const res = [];
            const seen = new Set();
            const todo = [formula.sub2, formula.sub1];
            while (todo.length > 0) {
                const conjunct = todo.pop();
                if (conjunct.operator == '∧') {
                    todo.push(conjunct.sub2, conjunct.sub1);
                    continue;
                }
                for (const cl of toCNF(conjunct)) {
                    const key = cnfClauseKey(cl);
                    if (seen.has(key)) continue; // duplicate clause
                    seen.add(key);
                    res.push(cl);
                }
            }
            return res;
        }
        throw new Error('internal error: cnf() requires a formula in NNF')
    }

    return toCNF(formula);
}

ModelFinder.prototype.cnfClauseKey = function(clause) {
    /**
     * Return a string key for <clause> for duplicate detection.
     * Clause must already be normalized + sorted.
     */
    return clause.cnfKey || (clause.cnfKey = clause.map(l => l.key()).join("\t"));
};

ModelFinder.prototype.cnfNormalizeClause = function(clause) {
    /**
     * Normalize <clause> by removing duplicates and contradictions, and sorting
     * literals in a canonical order. Return null if the clause is a tautology.
     */
    const seen = new Map(); // atom.key() -> +1 or -1
    const res = [];

    for (const lit of clause) {
        const atomKey = (lit.sub || lit).key();
        const pol = lit.sub ? -1 : 1;
        const prev = seen.get(atomKey);
        if (prev === -pol) return null; // tautology: p and ¬p both present
        if (prev === pol) continue;     // duplicate literal
        seen.set(atomKey, pol);
        res.push(lit);
    }

    res.sort((x, y) => x.key() < y.key() ? -1 : x.key() > y.key() ? 1 : 0);
    return res;
};


ModelFinder.prototype.definitionalCNF = function(formula) {
    /**
     * Convert <formula> (skolemized, NNF) into definitional CNF.
     *
     * An ordinary CNF is computed by multiplying out disjunctions: (A ∧ B) ∨ C
     * turns into (A ∨ C) ∧ (B ∨ C). This duplication of C can blow up
     * exponentially.
     *
     * A definitional CNF avoids the duplication by introducing new predicates
     * as names for subformulas. E.g., if we introduce $ as a name for A ∧ B, we
     * can turn (A ∧ B) ∨ C into $ ∨ C; we could then add $ ↔ (A ∧ B) to restore
     * equivalence. In fact, since <formula> is in NNF, it suffices to add $ →
     * (A ∧ B). For (A ∧ B) ∨ C, the resulting CNF is therefore
     *
     *    [$, C], [¬$, A], [¬$, B]
     *
     * instead of [A, C], [B, C]. C is no longer duplicated, at the price of a
     * new predicate.
     *
     * Every model of the original formula can be turned into a model of these
     * clauses by making $ true where A ∧ B is true, and every model of the
     * clauses is a model of <formula> once we ignore $.
     *
     * We have to be careful with free variables. Consider ∃xFx → ∃xGx.
     * Skolemized, this becomes ¬Fx ∨ Ga. The tseitin CNF of that is
     *
     * ($ ↔ ¬Fx) ∧ ($ ∨ Ga).
     *
     * If we create the instances of this universal requirement for all members
     * of domain { 0,1 }, we get
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
     * In general, a tseitin predicate $ for a formula S has to take an argument
     * for each free variable in S.
     * 
     * We don't name every non-literal subformula, but only those where a name
     * saves something ("renaming", in the sense of Boy de la Tour, "An
     * optimality result for clause form translation", 1992). 
     */
    var parser = this.parser;
    var defClauses = [];
    var MAX_DISTRIBUTE = 200;
    if (!this.tseitinPredicates) this.tseitinPredicates = {};
    var tseitinPredicates = this.tseitinPredicates;

    function hasQuantifier(f) {
        if (f.quantifier) return true;
        if (f.sub) return hasQuantifier(f.sub);
        if (f.sub1) return hasQuantifier(f.sub1) || hasQuantifier(f.sub2);
        return false;
    }

    function nameOf(f, boundVars) {
        // introduce P(x̄) for f and emit [¬P(x̄)] ∪ C for each clause C of f
        var varsInF = parser.getVariables(f);
        var vars = boundVars.filter(function(v) { return varsInF.includes(v) });
        var key = f.string+'|'+vars;
        if (tseitinPredicates[key]) return tseitinPredicates[key];
        var pSym = parser.getNewSymbol('$', 'tseitin predicate', vars.length);
        parser.predicateArgTypes[pSym] = vars.map(function(v) {
            return parser.expressionType[v];
        });
        var p = new AtomicFormula(pSym, vars);
        tseitinPredicates[key] = p;
        var inner = cnfOf(f, boundVars);
        if (inner === null) return null;
        var negp = new NegatedFormula(p);
        for (var i=0; i<inner.length; i++) defClauses.push([negp].concat(inner[i]));
        return p;
    }

    function cnfOf(f, boundVars) {
        if (f.type == 'literal') return [[f]];
        if (f.quantifier == '∃') return null;
        if (f.quantifier) { // ∀: drop it, the variable stays universal
            return cnfOf(f.matrix, boundVars.concat([f.variable]));
        }
        if (f.operator == '∧') {
            var a = cnfOf(f.sub1, boundVars), b = cnfOf(f.sub2, boundVars);
            if (a === null || b === null) return null;
            return a.concat(b);
        }
        if (f.operator != '∨') return null;
        var sides = [f.sub1, f.sub2].map(function(sub) {
            // a quantified disjunct gets a name; otherwise its variables would
            // be merged into every clause the other side contributes
            if (hasQuantifier(sub)) {
                var p = nameOf(sub, boundVars);
                return p === null ? null : [[p]];
            }
            return cnfOf(sub, boundVars);
        });
        if (sides.includes(null)) return null;
        if (sides[0].length * sides[1].length > MAX_DISTRIBUTE) {
            var p = nameOf(f.sub2, boundVars);
            if (p === null) return null;
            sides[1] = [[p]];
        }
        var res = [];
        for (var i=0; i<sides[0].length; i++)
            for (var j=0; j<sides[1].length; j++)
                res.push(sides[0][i].concat(sides[1][j]));
        return res;
    }

    var top = cnfOf(formula, []);
    return defClauses.concat(top);
}

ModelFinder.prototype.eliminateUniversalTseitinPredicates = function(clauses) {
    /**
     * Simplify <clauses> by eliminating tseitin predicates asserted
     * universally true or false via a unit clause [±P(v1,..,vn)] where
     * v1..vn are distinct variables. Such P can be replaced by true/false in
     * every clause, letting us skip cell creation for it.
     *
     * Iterates to fixed point: dropping literals can create new unit
     * clauses. Returns the simplified clause list.
     **/
    var parser = this.parser;
    var alwaysTrue = {};
    var alwaysFalse = {};
    var nl = clauses;
    var changed = true;
    while (changed) {
        changed = false;
        for (var i = 0; i < nl.length; i++) {
            if (nl[i].length !== 1) continue;
            var lit = nl[i][0];
            var atom = lit.sub || lit;
            if (parser.expressionType[atom.predicate] !== 'tseitin predicate') continue;
            // All args must be distinct variables:
            var terms = atom.terms;
            var seenVar = {};
            var ok = true;
            for (var j = 0; j < terms.length; j++) {
                var t = terms[j];
                if (t.isArray) { ok = false; break; } // function term
                var etype = parser.expressionType[t];
                if (!etype || etype.indexOf('variable') === -1) { ok = false; break; }
                if (seenVar[t]) { ok = false; break; }
                seenVar[t] = true;
            }
            if (!ok) continue;
            var pred = atom.predicate;
            var isPos = !lit.sub;
            if (isPos) {
                if (alwaysTrue[pred]) continue;
                if (alwaysFalse[pred]) return [[]];
                alwaysTrue[pred] = true;
            } else {
                if (alwaysFalse[pred]) continue;
                if (alwaysTrue[pred]) return [[]];
                alwaysFalse[pred] = true;
            }
            changed = true;
        }
        if (!changed) break;
        var nl2 = [];
        var seen = new Set();
        for (var i = 0; i < nl.length; i++) {
            var clause = nl[i];
            var newClause = [];
            var satisfied = false;
            for (var j = 0; j < clause.length; j++) {
                var clit = clause[j];
                var cpred = (clit.sub || clit).predicate;
                var cpos = !clit.sub;
                if (alwaysTrue[cpred]) {
                    if (cpos) { satisfied = true; break; }
                    continue;
                }
                if (alwaysFalse[cpred]) {
                    if (!cpos) { satisfied = true; break; }
                    continue;
                }
                newClause.push(clit);
            }
            if (satisfied) continue;
            if (newClause.length === 0) return [[]];
            var key = this.cnfClauseKey(newClause);
            if (seen.has(key)) continue;
            seen.add(key);
            nl2.push(newClause);
        }
        nl = nl2;
    }
    return nl;
};

ModelFinder.prototype.simplifyClauses = function(clauseList) {
    /**
     * Simplify <clauseList>.
     */

    // Remove duplicates and tautologies that might have been introduced by
    // combining CNFs:
    const nl = [];
    const seen = new Set();
    for (const cl of clauseList) {
        const norm = this.cnfNormalizeClause(cl);
        if (norm === null) continue; // tautology -> drop
        const key = this.cnfClauseKey(norm);
        if (seen.has(key)) continue;
        seen.add(key);
        nl.push(norm);
    }

    nl.sort((a, b) => a.length - b.length);

    // If clause A is a subset of (or equal to) clause B, clause B can be
    // removed (e.g. [[p],[p,q]] => [[p]] or [[q,s],[p,q,r,s]] => [[q,s]]. The
    // naive way to test this is O(n!). The following still takes too long if we
    // have a lot of clauses.
    if (nl.length > 1000) {
        log('too many clauses to simplify by subset testing');
        return nl;
    }
    // We store which clauses contain which literals: q => [c1,c2],...
    var clauseIndex = new Map();
    var literals2clauses = {};
    for (var i=0; i<nl.length; i++) {
        clauseIndex.set(nl[i], i);
        for (var k=0; k<nl[i].length; k++) {
            var lit = nl[i][k].key();
            if (!literals2clauses[lit]) literals2clauses[lit] = [nl[i]];
            else literals2clauses[lit].push(nl[i]);
        }
    }
    // We look for supersets of each clause and mark them for removal:
    var removed = new Set();
    for (var i=0; i<nl.length; i++) {
        var clause = nl[i];
        var lit = clause[0].key();
        // slice() because intersect() mutates its receiver, and
        // literals2clauses[lit] is shared across iterations.
        var supersets = literals2clauses[lit].slice();
        for (var k=1; k<clause.length && supersets.length; k++) {
            lit = clause[k].key();
            supersets.intersect(literals2clauses[lit]);
        }
        for (var k=0; k<supersets.length; k++) {
            if (clauseIndex.get(supersets[k]) > i) {
                removed.add(supersets[k]);
            }
        }
    }
    return nl.filter(function(cl) { return !removed.has(cl); });
}

ModelFinder.prototype.nextStep = function() {
    /**
     * Try to find a model for the current domain size; returns true when a
     * model is found.
     *
     * The search has two phases:
     *
     * First, grounding and initial propagation. We begin by replacing
     * universally quantified variables in clauses by domain elements in every
     * possible way. E.g., with domain {0,1}, the clause [Ff(x)] becomes two
     * ground clauses [Ff(0)] and [Ff(1)]. As each ground clause is added, we
     * immediately simplify it against cell values that are already known (e.g.
     * from pre-assigned equality cells). If a ground clause contains a single
     * literal (is "unit"), the literal must be true; this may shrink other
     * clauses, which may lead to new unit clauses, and so on.
     *
     * In phase 2, we pick an unassigned expression ("cell"), try each of its
     * possible values and propagate the result to all clauses containing the
     * expression. This can again shrink clauses and force the interpretation of
     * other expressions, etc. On contradiction, we backtrack.
     *
     * If all values for the top-level cell are exhausted, no model exists at
     * this domain size, so we increase the domain and start over.
     */
    log('=== searching for model: '+this.model.domain.length+' individuals'+(this.model.isModal ? ', '+this.model.worlds.length+' worlds' : '')+' ===');

    // Phase 1: Grounding. Done incrementally so as not to block the browser.
    if (!this.model.groundingDone) {
        log('grounding');
        this.model.groundIncremental(50); // 50ms budget
        if (!this.model.groundingDone) return false; // more grounding to do
        if (!this.model.initOk) {
            log('initial grounding/propagation found contradiction; no model at this domain size');
            this.increaseDomain();
            return false;
        }
        // grounding finished; set up initial search state:
        var cell = this.model.selectCell();
        if (!cell) {
            log('*** model found by initial propagation (no branching needed) ***');
            this.model.buildInterpretation();
            this.model.checkModel();
            return true;
        }
        log('grounding done: '+this.model.unassignedCount()+' cells to assign, '+this.model.activeClauseCount()+' active clauses; first branch on '+cell.id+' ('+cell.possible.length+' values)');
        // The searchStack is a stack of {cell, valueIdx, trailMark} objects,
        // where cell is the cell we are branching on at this level, valueIdx is
        // the index of the next value to try for that cell, and trailMark is
        // the index in the model's trail to which we should undo when we
        // backtrack to this level.
        this.searchStack.push({cell: cell, valueIdx: 0, trailMark: this.model.trail.length});
    }

    // Phase 2: Search loop.
    for (let step = 0; step < 100; step++) {
        if (this.searchStack.length === 0) {
            log('search space exhausted at this domain size');
            this.increaseDomain();
            return false;
        }

        var searchPoint = this.searchStack[this.searchStack.length - 1];
        var depth = this.searchStack.length;

        // Undo previous attempt at this level:
        this.model.undoToMark(searchPoint.trailMark);
        searchPoint.trailMark = this.model.trail.length;

        // Get values for this cell:
        var values = this.model.getCellValues(searchPoint.cell);
        if (searchPoint.valueIdx >= values.length) {
            // All values exhausted — backtrack
            log('[d'+depth+'] '+searchPoint.cell.id+': all '+values.length+' values exhausted, backtracking');
            this.searchStack.pop();
            continue;
        }

        var value = values[searchPoint.valueIdx];
        searchPoint.valueIdx++;
        log('[d'+depth+'] try '+searchPoint.cell.id+' = '+value+' ('+searchPoint.valueIdx+'/'+values.length+')');

        var ok = this.model.assignCell(searchPoint.cell, value);
        if (ok) {
            var nextCell = this.model.selectCell();
            if (!nextCell) {
                log('*** model found at depth '+depth+' ***');
                this.model.buildInterpretation();
                this.model.checkModel();
                return true;
            }
            log('[d'+(depth+1)+'] next branch: '+nextCell.id+' ('+nextCell.possible.length+' values, '+this.model.unassignedCount()+' cells remain)');
            this.searchStack.push({cell: nextCell, valueIdx: 0, trailMark: this.model.trail.length});
        }
        // If !ok, valueIdx is already incremented; loop tries the next value.
    }

    return false;
}

ModelFinder.prototype.increaseDomain = function() {
    /**
     * No model found at current domain size; increase and try again.
     */
    var numWorlds = this.model.worlds.length;
    var numIndividuals = this.model.domain.length;
    log('no model with '+numIndividuals+' individuals'+(numWorlds ? ', '+numWorlds+' worlds' : '')+'; increasing domain');
    if (numWorlds) {
        if (this.parser.isPropositional) {
            numWorlds++;
        }
        else {
            if (numIndividuals > 1) {
                numIndividuals -= 1;
                numWorlds += 1;
            }
            else {
                var total = numWorlds + numIndividuals + 1;
                // We try through all models with that total, starting with 1
                // world and the rest individuals, then increasing the worlds
                // and decreasing the individuals.
                numWorlds = 1;
                numIndividuals = total - 1;
            }
        }
    }
    else {
        numIndividuals++;
    }
    log('new domain size: '+numIndividuals+' individuals'+(numWorlds ? ', '+numWorlds+' worlds' : ''));
    this.model = new Model(this, numIndividuals, numWorlds);
    this.searchStack = [];
}

function Model(modelfinder, numIndividuals, numWorlds) {
    /**
     * A (partial) model.
     */

    this.modelfinder = modelfinder;
    this.parser = modelfinder.parser;

    // initialize domains:
    this.domain = Array.getArrayOfNumbers(numIndividuals);
    this.worlds = Array.getArrayOfNumbers(numWorlds);
    this.isModal = numWorlds > 0;
    log('initialised model domain '+this.domain+', worlds '+this.worlds);

    // list of all terms that we need to interpret:
    var terms = this.getTerms();
    this.indivTerms = terms[0];
    this.worldTerms = terms[1];

    // build cells:
    this.cells = [];
    this.cellIndex = {};  // cell id string -> Cell
    this.groundClauses = [];
    this.trail = [];
    this.createCells();

    // grounding state (for incremental grounding):
    this.groundingDone = false;
    this.initOk = true;
    this.groundingQueue = [];
    this.clauseInfos = this.prepareClauseInfos();
    this.groundingClauseIdx = 0;
    this.groundingTuple = null;  // null = start of new clause
    this.rootedWorldClausesAdded = false;

    // interpretation function (populated when model is found):
    this.interpretation = {};

}

function Cell(id, symbol, args, possibleValues, isFunction) {
    /**
     * A cell represents an entry in the model's interpretation function.
     *
     * There are two kinds of cells:
     *
     *   - Function cells (isFunction = true): these give the value of a
     *     function symbol or constant for specific arguments. For example, the
     *     constant 'a' has a cell whose value is an element of the domain
     *     (e.g. 0 or 1). The function symbol 'f' at argument tuple (0,1) has a
     *     cell for f(0,1). Function cell values are domain elements (numbers).
     *
     *   - Predicate cells (isFunction = false): these give the truth-value of
     *     a predicate for specific arguments. For example, the predicate 'F' at
     *     argument (0) has a cell for F(0). Predicate cell values are booleans.
     *
     * The search works by assigning values to cells one at a time. Each
     * assignment can trigger propagation: if a clause becomes unit (only one
     * unresolved literal), the remaining literal's cell is forced.
     *
     * <id> is a string that uniquely identifies this cell
     * <symbol> is the function/predicate symbol name.
     * <args> is the argument tuple (array of domain element numbers).
     * <possibleValues> is the initial list of values this cell might take.
     * <isFunction> distinguishes function cells from predicate cells.
     */
    this.id = id;
    this.symbol = symbol;
    this.args = args;
    this.value = null;
    this.possible = possibleValues.slice();
    this.isFunction = isFunction;
    this.occurrences = [];    // [{clauseIdx, litIdx}]: which ground clause
                              // literals mention this cell; used to trigger
                              // re-evaluation when this cell is assigned
    this.occurrenceKeys = new Set();
    this.fixed = false;    // true for cells whose value is pre-determined
                           // (e.g. equality cells: =(i,j) is true iff i===j)
    this.maxIndex = 0;
    for (var i=0; i<args.length; i++) {
        if (args[i] > this.maxIndex) this.maxIndex = args[i];
    }
}

function GroundClause(index, literals) {
    /**
     * A ground clause is a disjunction of ground literals (no variables),
     * stored as an array of GroundLiteral objects. During search, literals can
     * become "inactive" (known false under current assignments) or the whole
     * clause can become satisfied (at least one literal is true). When only
     * one literal remains active, the clause is unit and forces that
     * literal's cell to a specific value (unit propagation).
     */
    this.index = index;
    this.literals = literals;
    this.satisfied = false;
    this.numActive = literals.length;
}

function GroundLiteral(positive, predicate, terms, termCellIds) {
    /**
     * A ground literal is a literal in which all variables have been replaced
     * by domain elements. The terms may still contain unevaluated function
     * applications (e.g. [f,0,1]) whose values depend on function cells that
     * haven't been assigned yet.
     *
     * <termCellIds> lists the cell ids of any function subterms so that when
     * those cells are assigned, this literal can be re-evaluated.
     */
    this.positive = positive;   // true if positive literal
    this.predicate = predicate; // predicate symbol string
    this.terms = terms;         // the terms array (may contain function term arrays)
    this.termCellIds = termCellIds; // list of function cell ids in subterms
    this.active = true;         // false once this literal is known to be false
                                // under the current (partial) assignment
}

Model.prototype.createCells = function() {
    /**
     * Create one Cell for every slot in the interpretation that needs a
     * value in this.cells. Specifically:
     *
     *   - For each constant symbol c: one cell (value = a domain element).
     *   - For each n-ary function symbol f and each n-tuple of domain
     *     elements: one cell for f(d1,...,dn) (value = a domain element).
     *   - For each n-ary predicate P and each n-tuple of (appropriately
     *     typed) domain elements: one cell for P(d1,...,dn) (value = boolean).
     *   - For each 0-ary predicate (sentence letter) p: one cell (value =
     *     boolean).
     *
     * Equality cells (=) are pre-assigned: =(i,j) is true iff i===j.
     *
     * In modal logic, predicates take a world as their last argument, and the
     * accessibility relation R takes two worlds; the domains for each argument
     * position are set accordingly.
     */
    var parser = this.parser;

    for (var i=0; i<parser.symbols.length; i++) {
        var s = parser.symbols[i];
        var stype = parser.expressionType[s];

        if (stype == 'individual constant' || stype == 'world constant') {
            var cellId = s;
            var valueDomain = (stype == 'world constant') ? this.worlds : this.domain;
            var cell = new Cell(cellId, s, [], valueDomain.slice(), true);
            this.cells.push(cell);
            this.cellIndex[cellId] = cell;
        }
        else if (stype.indexOf('function symbol') > -1) {
            var arity = parser.arities[s];
            var isWorld = stype.indexOf('world') > -1;
            var valueDomain = isWorld ? this.worlds : this.domain;
            var argDomains = this.getFunctionArgDomains(s, arity);
            var tuples = Model.getMixedTuples(argDomains);
            for (var j=0; j<tuples.length; j++) {
                var args = tuples[j];
                var termArr = [s].concat(args);
                var cellId = termArr.toString(); // e.g. '[f,0,1]'
                var cell = new Cell(cellId, s, args, valueDomain.slice(), true);
                this.cells.push(cell);
                this.cellIndex[cellId] = cell;
            }
        }
        else if (stype.indexOf('predicate') > -1 || stype.indexOf('sentence letter') > -1) {
            var arity = parser.arities[s] || 0;
            if (arity == 0) {
                var cellId = s + '[]';
                var cell = new Cell(cellId, s, [], [false, true], false);
                this.cells.push(cell);
                this.cellIndex[cellId] = cell;
            }
            else {
                // For predicates, we need to handle mixed argument types
                // (some args are worlds, some individuals) in modal logic.
                var argDomains = this.getPredicateArgDomains(s, arity);
                var tuples = Model.getMixedTuples(argDomains);
                for (var j=0; j<tuples.length; j++) {
                    var args = tuples[j];
                    var cellId = s + args.toString(); // e.g. 'F[0,1]'
                    var cell = new Cell(cellId, s, args, [false, true], false);
                    this.cells.push(cell);
                    this.cellIndex[cellId] = cell;
                }
            }
        }
    }

    // Pre-assign equality cells (only if equality is in the signature):
    // In modal logic, equality has an extra world argument: =(i,j,w).
    // Equality holds iff i===j, regardless of world.
    if (this.parser.expressionType['=']) {
        var eqWorlds = this.worlds.length > 0 ? this.worlds : [null];
        for (var i=0; i<this.domain.length; i++) {
            for (var j=0; j<this.domain.length; j++) {
                for (var wi=0; wi<eqWorlds.length; wi++) {
                    var args = eqWorlds[wi] !== null ? [i,j,eqWorlds[wi]] : [i,j];
                    var cellId = '=' + args.toString();
                    var cell = this.cellIndex[cellId];
                    if (cell) {
                        cell.value = (i === j);
                        cell.possible = [];
                        cell.fixed = true;
                    }
                }
            }
        }
    }

    log('created '+this.cells.length+' cells');
};

Model.prototype.getPredicateArgDomains = function(predicate, arity) {
    /**
     * Return array of domains for each argument position of a predicate.
     * In modal logic, the last argument of user predicates is a world,
     * the accessibility relation R takes two worlds, and tseitin predicates
     * may have worlds in any argument position (per parser.predicateArgTypes).
     */
    var domains = [];
    if (!this.isModal) {
        for (var i=0; i<arity; i++) domains.push(this.domain);
        return domains;
    }
    var parser = this.parser;
    var argTypes = parser.predicateArgTypes[predicate];
    if (argTypes) {
        var self = this;
        return argTypes.map(function(t) {
            return t === 'world variable' ? self.worlds : self.domain;
        });
    }
    for (var i=0; i<arity; i++) {
        // R takes two world arguments; other predicates have world as last arg
        if (predicate === parser.R) {
            domains.push(this.worlds);
        }
        else if (i === arity - 1) {
            domains.push(this.worlds);
        }
        else {
            domains.push(this.domain);
        }
    }
    return domains;
};

Model.prototype.getFunctionArgDomains = function(funcSymbol, arity) {
    /**
     * Return array of domains for each argument position of a function symbol.
     * Skolem functions may take world-variable arguments (e.g. f(w) from
     * skolemizing ∀w∃x...); the argument types are recorded in
     * parser.functionArgTypes during skolemization.
     */
    var argTypes = this.parser.functionArgTypes[funcSymbol];
    if (argTypes) {
        var self = this;
        return argTypes.map(function(t) {
            return t === 'world variable' ? self.worlds : self.domain;
        });
    }
    // fallback for non-skolem functions? xxx check
    var isWorld = this.parser.expressionType[funcSymbol].indexOf('world') > -1;
    var domain = isWorld ? this.worlds : this.domain;
    var domains = [];
    for (var i=0; i<arity; i++) domains.push(domain);
    return domains;
};

Model.getMixedTuples = function(argDomains) {
    /**
     * Return all tuples where position i ranges over argDomains[i].
     */
    if (argDomains.length == 0) return [[]];
    var res = [];
    var tuple = Array.getArrayOfZeroes(argDomains.length);
    var maxValues = argDomains.map(function(d) { return d.length - 1; });
    res.push(tuple.copy());
    while (Model.iterateTuple(tuple, maxValues)) {
        res.push(tuple.copy());
    }
    return res;
};


Model.prototype.prepareClauseInfos = function() {
    /**
     * Prepare clause metadata for incremental grounding. For each clause, we
     * pre-compute the list of variables and the maximum domain index for each
     * variable (individual vs. world), which is needed to enumerate all ground
     * substitutions.
     */
    var parser = this.parser;
    var clauses = this.modelfinder.clauses;
    var clauseInfos = [];
    for (var c = 0; c < clauses.length; c++) {
        var variables = [];
        for (var i = 0; i < clauses[c].length; i++) {
            variables.extendNoDuplicates(parser.getVariables(clauses[c][i]));
        }
        var maxValues = [];
        for (var vi = 0; vi < variables.length; vi++) {
            maxValues.push(parser.expressionType[variables[vi]] == 'variable' ? this.domain.length - 1 : this.worlds.length - 1);
        }
        clauseInfos.push({clause: clauses[c], variables: variables, maxValues: maxValues});
    }
    clauseInfos.sort(function(a, b) { return a.variables.length - b.variables.length; });
    return clauseInfos;
};

Model.prototype.groundIncremental = function(timeLimit) {
    /**
     * Incrementally ground clauses, simplify, and propagate.
     *
     * After replacing variables with numerals ("grounding"), we simplify all
     * clauses based on already-known cell values; if a clause becomes unit,
     * this may force another cell value, which we propagate further, etc.
     *
     * Sets this.groundingDone = true when all clauses have been grounded.
     * Sets this.initOk = false if a contradiction is found (meaning no model
     * exists at this domain size).
     */
    var t0 = performance.now();
    var queue = this.groundingQueue;

    var self = this;
    function processClause(groundClause) {
        if (!self.addSimplifiedClause(groundClause, queue) || !self.drainQueue(queue)) {
            self.initOk = false;
            self.groundingDone = true;
            return false;
        }
        return true;
    }

    while (this.groundingClauseIdx < this.clauseInfos.length) {
        var info = this.clauseInfos[this.groundingClauseIdx];
        var clause = info.clause;
        var variables = info.variables;

        if (variables.length === 0) {
            if (!processClause(clause)) return;
            this.groundingClauseIdx++;
            this.groundingTuple = null;
            continue;
        }

        // Initialize tuple if starting a new clause:
        if (!this.groundingTuple) {
            this.groundingTuple = Array.getArrayOfZeroes(variables.length);
        }

        // Process ground instances of this clause:
        do {
            var interpretation = this.groundingTuple;
            var nclause = clause.map(function(formula) {
                var nformula = formula;
                for (var j = 0; j < variables.length; j++) {
                    nformula = nformula.substitute(variables[j], interpretation[j]);
                }
                return nformula;
            });
            if (!processClause(nclause)) return;
            if (performance.now() - t0 > timeLimit) return;
        } while (Model.iterateTuple(this.groundingTuple, info.maxValues));

        // Clause fully grounded — move to next:
        this.groundingClauseIdx++;
        this.groundingTuple = null;
    }

    // Require every non-root world to be reachable from w0:
    if (!this.rootedWorldClausesAdded) {
        this.rootedWorldClausesAdded = true;
        if (!this.addRootedWorldClauses(queue)) {
            this.initOk = false;
            this.groundingDone = true;
            return;
        }
    }

    log(this.groundClauses.length + ' ground clauses after simplification');
    this.groundingDone = true;
};

Model.prototype.addSimplifiedClause = function(formulaClause, queue) {
    /**
     * Add a newly-grounded clause to the model. But first simplify against
     * current cell assignments.
     *
     * The surviving literals are converted to GroundLiteral objects, wrapped
     * in a GroundClause, and registered on the relevant cells' occurrence
     * lists so that future cell assignments trigger re-evaluation.
     *
     * Returns false on contradiction, true otherwise.
     */
    var lits = [];
    var skip = false;
    for (var li = 0; li < formulaClause.length; li++) {
        var tv = this.evaluateFormula(formulaClause[li]);
        if (tv === true) {
            skip = true;
            break; // clause satisfied — skip entirely
        }
        if (tv === false) {
            continue; // literal is false — drop it
        }
        // Indeterminate — keep the literal:
        lits.push(formulaClause[li]);
    }
    if (skip) return true;
    if (lits.length === 0) return false; // contradiction: empty clause

    // Check for tautology (complementary literals) and drop duplicate
    // literals. Grounding can introduce both even though the input CNF had
    // none (e.g. [Fx,¬Fy] with x=y, or [¬Lf(0,0)0,¬Lf(0,0)y] with y=0).
    var atomPol = new Map(); // atom.key() -> +1 (positive) or -1 (negated)
    var deduped = [];
    for (var i = 0; i < lits.length; i++) {
        var atom = lits[i].sub || lits[i];
        var atomKey = atom.key();
        var pol = lits[i].sub ? -1 : 1;
        var prev = atomPol.get(atomKey);
        if (prev === -pol) return true; // tautology — skip clause
        if (prev === pol) continue;     // duplicate literal — drop
        atomPol.set(atomKey, pol);
        deduped.push(lits[i]);
    }
    lits = deduped;

    // Convert to GroundLiteral/GroundClause objects:
    var ci = this.groundClauses.length;
    var groundLits = [];
    for (var li = 0; li < lits.length; li++) {
        var formula = lits[li];
        var atom = formula.sub || formula;
        var positive = (atom === formula);
        var predicate = atom.predicate;
        var terms = atom.terms;
        var termCellIds = this.collectTermCellIds(terms);
        groundLits.push(new GroundLiteral(positive, predicate, terms, termCellIds));
    }
    var gc = new GroundClause(ci, groundLits);
    this.groundClauses.push(gc);

    // Register occurrences on cells:
    for (var li = 0; li < groundLits.length; li++) {
        var lit = groundLits[li];
        var occ = {clauseIdx: ci, litIdx: li};

        var reducedTerms = this.reduceTermsFromCells(lit.terms);
        var allGround = true;
        for (var ti = 0; ti < reducedTerms.length; ti++) {
            if (typeof reducedTerms[ti] !== 'number') { allGround = false; break; }
        }
        if (allGround) {
            var predCellId = lit.predicate + reducedTerms.toString();
            if (this.cellIndex[predCellId]) {
                this.registerOccurrence(this.cellIndex[predCellId], occ);
            }
        }

        for (var ti = 0; ti < lit.termCellIds.length; ti++) {
            var tcid = lit.termCellIds[ti];
            if (this.cellIndex[tcid]) {
                this.registerOccurrence(this.cellIndex[tcid], occ);
            }
        }

        // Cross-off registration for unit clauses with function terms:
        if (lits.length === 1 && !allGround) {
            var funcInfo = this.identifyFunctionTerm(reducedTerms);
            if (funcInfo) {
                lit.funcArgPos = funcInfo.pos;
                lit.funcCellId = funcInfo.cellId;
                var funcCell = this.cellIndex[funcInfo.cellId];
                var valueDomain = funcCell ? funcCell.possible : this.domain;
                for (var vi = 0; vi < valueDomain.length; vi++) {
                    var args = reducedTerms.slice();
                    args[funcInfo.pos] = valueDomain[vi];
                    var predCellId = lit.predicate + args.toString();
                    if (this.cellIndex[predCellId]) {
                        this.registerOccurrence(this.cellIndex[predCellId], occ);
                    }
                }
            }
        }
    }

    // If unit clause, try to force immediately:
    if (gc.numActive === 1) {
        var forced = this.forceLiteral(gc);
        if (forced === false) return false;
        if (forced) queue.push(forced);
    }

    return true;
};

Model.prototype.addRootedWorldClauses = function(queue) {
    /**
     * Add clauses requiring every non-root world to be reachable from
     * a previous world (and ultimately from w0):
     * 
     *   R(0,w) ∨ R(1,w) ∨ ... ∨ R(w-1,w)   for each w > 0
     */
    if (!this.isModal) return true;
    if (this.modelfinder.s5) return true;
    var R = this.parser.R;
    log('adding clauses to make the model connected');
    for (var w = 1; w < this.worlds.length; w++) {
        var clause = [];
        for (var u = 0; u < w; u++) {
            clause.push(new AtomicFormula(R, [u, w]));
        }
        if (!this.addSimplifiedClause(clause, queue)) return false;
        if (!this.drainQueue(queue)) return false;
    }
    return true;
};

Model.prototype.evaluateFormula = function(formula) {
    /**
     * Evaluate a ground Formula object against current cell assignments.
     * Returns true if satisfied, false if falsified, null if indeterminate.
     */
    var atom = formula.sub || formula;
    var positive = (atom === formula);
    var predicate = atom.predicate;

    // Reduce terms using known cell values:
    var reducedTerms = this.reduceTermsFromCells(atom.terms);

    // Check if all terms are ground numbers:
    for (var i = 0; i < reducedTerms.length; i++) {
        if (typeof reducedTerms[i] !== 'number') return null;
    }

    // Equality:
    if (predicate === '=') {
        var eqVal = (reducedTerms[0] === reducedTerms[1]);
        return positive ? eqVal : !eqVal;
    }

    var predCellId = predicate + reducedTerms.toString();
    var predCell = this.cellIndex[predCellId];
    if (!predCell) return null;
    if (predCell.value === null) return null;
    return positive ? predCell.value : !predCell.value;
};

Model.prototype.drainQueue = function(queue) {
    /**
     * Process the propagation queue: assign each forced {cell, value} pair,
     * then re-evaluate all clauses that mention the newly assigned cell (which
     * may produce more forced assignments). Continues until the queue is empty
     * or a contradiction is found. Returns false on contradiction.
     *
     * Used during phase 1 (grounding) to propagate consequences of unit clauses.
     */
    while (queue.length > 0) {
        var forced = queue.shift();
        if (forced.cell.value !== null) {
            if (forced.cell.value !== forced.value) {
                log('  conflict: '+forced.cell.id+' already '+forced.cell.value+', cannot force '+forced.value);
                return false;
            }
            continue;
        }
        log('  forced '+forced.cell.id+' = '+forced.value);
        this.trail.push({type: 'assign', cell: forced.cell, oldPossible: forced.cell.possible});
        forced.cell.value = forced.value;
        forced.cell.possible = [];
        if (!this.processOccurrences(forced.cell, queue)) {
            return false;
        }
    }
    return true;
};

Model.prototype.identifyFunctionTerm = function(reducedTerms) {
    /**
     * If <reducedTerms> has exactly one non-ground position (a function term
     * whose arguments are all ground), return {pos, cellId} identifying it.
     * Otherwise return null.
     */
    var funcPos = -1;
    for (var i=0; i<reducedTerms.length; i++) {
        if (typeof reducedTerms[i] !== 'number') {
            if (funcPos >= 0) return null; // more than one non-ground term
            funcPos = i;
        }
    }
    if (funcPos < 0) return null;
    var term = reducedTerms[funcPos];
    if (!term.isArray) return null;
    // Check all arguments of the function term are ground:
    for (var i=1; i<term.length; i++) {
        if (typeof term[i] !== 'number') return null;
    }
    return {pos: funcPos, cellId: term.toString()};
};

Model.prototype.collectTermCellIds = function(terms) {
    /**
     * Return list of function/constant cell ids appearing in <terms>.
     */
    var ids = [];
    for (var i=0; i<terms.length; i++) {
        this.collectTermCellIdsRec(terms[i], ids);
    }
    return ids;
};

Model.prototype.collectTermCellIdsRec = function(term, ids) {
    if (typeof term === 'number') return;
    if (term.isArray) {
        // function term like [f, 0, a] or [f, [g, 0]]
        // First collect from arguments:
        for (var i=1; i<term.length; i++) {
            this.collectTermCellIdsRec(term[i], ids);
        }
        // Then try to build this cell's id by reducing arguments:
        var reduced = this.reduceTermFromCells(term);
        if (typeof reduced !== 'number') {
            // term is not fully reduced; the cell id is the reduced form
            var cellId = reduced.toString();
            if (this.cellIndex[cellId] && ids.indexOf(cellId) === -1) {
                ids.push(cellId);
            }
        }
    }
    else {
        // constant string like 'a'
        if (this.cellIndex[term] && ids.indexOf(term) === -1) {
            ids.push(term);
        }
    }
};

Model.prototype.reduceTermFromCells = function(term) {
    /**
     * Reduce a single term by substituting known cell values.
     * Returns a number if the term is fully reduced, or the partially
     * reduced term otherwise.
     */
    if (typeof term === 'number') return term;
    if (term.isArray) {
        var nterm = [term[0]];
        for (var i=1; i<term.length; i++) {
            nterm.push(this.reduceTermFromCells(term[i]));
        }
        var cell = this.cellIndex[nterm.toString()];
        if (cell && cell.value !== null) return cell.value;
        return nterm;
    }
    // constant string
    var cell = this.cellIndex[term];
    if (cell && cell.value !== null) return cell.value;
    return term;
};

Model.prototype.reduceTermsFromCells = function(terms) {
    /**
     * Reduce all terms by substituting known cell values.
     */
    var res = [];
    for (var i=0; i<terms.length; i++) {
        res.push(this.reduceTermFromCells(terms[i]));
    }
    return res;
};

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
        else if (stype.indexOf('function symbol') > -1) {
            var arity = this.parser.arities[s];
            var isWorldResult = stype.indexOf('world') > -1;
            var targetList = isWorldResult ? worldTerms : indivTerms;
            var argDomains = this.getFunctionArgDomains(s, arity);
            Model.getMixedTuples(argDomains).forEach(function(li) {
                li.unshift(s);
                targetList.push(li.toString());
            });
        }
    }
    indivTerms.sort(function(a,b){ return a.length - b.length; });
    worldTerms.sort(function(a,b){ return a.length - b.length; });
    return [indivTerms, worldTerms];
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
    // log("maxValue "+maxValue);
    return maxValue;
}

Model.prototype.undoToMark = function(mark) {
    /**
     * Undo all trail entries from the current position back to <mark>.
     *
     * The trail is an append-only log of every state change made during search:
     * cell assignments, value eliminations, clause satisfactions, and literal
     * deactivations. Each search-stack point records a "mark": the trail length
     * at entry. To backtrack, we pop trail entries back to that mark, reversing
     * each change.
     */
    while (this.trail.length > mark) {
        var entry = this.trail.pop();
        switch (entry.type) {
        case 'assign':
            entry.cell.value = null;
            entry.cell.possible = entry.oldPossible;
            break;
        case 'eliminate':
            entry.cell.possible.push(entry.value);
            break;
        case 'satisfy':
            entry.clause.satisfied = false;
            break;
        case 'deactivate':
            entry.clause.literals[entry.litIdx].active = true;
            entry.clause.numActive++;
            break;
        }
    }
};

Model.prototype.assignCell = function(cell, value) {
    /**
     * Assign <value> to <cell> and propagate all consequences.
     * Returns true if the assignment is consistent, false if a contradiction
     * is found (an empty clause).
     */
    // Record on trail:
    this.trail.push({type: 'assign', cell: cell, oldPossible: cell.possible});
    cell.value = value;
    cell.possible = [];

    // Propagation queue: list of {cell, value} pairs forced by unit clauses:
    var queue = [];

    // Process all occurrences of this cell, then drain the propagation queue:
    if (!this.processOccurrences(cell, queue)) return false;
    return this.drainQueue(queue);
};

Model.prototype.processOccurrences = function(cell, queue) {
    /**
     * After <cell> has been assigned a value, re-evaluate every literal that
     * depends on this cell (via the cell's occurrence list). For each literal:
     *
     *   - If the literal is now true: mark the clause as satisfied.
     *   - If the literal is now false: deactivate it and decrement the
     *     clause's active-literal count. If the count hits zero, we have a
     *     contradiction. If it hits one, the clause is unit and we push a
     *     forced assignment onto <queue> for the remaining literal.
     *   - If the literal is still indeterminate (depends on other unassigned
     *     cells): no action, but we may register new cell dependencies
     *     discovered via partial term reduction.
     *
     * Also handles "cross-off" propagation for unit clauses whose sole
     * literal contains an unresolved function term: if the predicate cell is
     * assigned a value that violates the literal, the function-cell value that
     * would map to this predicate cell is eliminated from its domain.
     *
     * Returns false on contradiction, true otherwise.
     */
    for (var oi=0; oi<cell.occurrences.length; oi++) {
        var occ = cell.occurrences[oi];
        var gc = this.groundClauses[occ.clauseIdx];
        if (gc.satisfied) continue;

        var lit = gc.literals[occ.litIdx];
        if (!lit.active) continue;

        // Try to evaluate this literal with current cell values:
        var tv = this.evaluateLiteral(lit, occ);
        // tv is true, false, or null (indeterminate)

        if (tv === true) {
            // Literal is true: clause is satisfied
            this.trail.push({type: 'satisfy', clause: gc});
            gc.satisfied = true;
        }
        else if (tv === false) {
            // Literal is false: deactivate it
            this.trail.push({type: 'deactivate', clause: gc, litIdx: occ.litIdx});
            lit.active = false;
            gc.numActive--;
            if (gc.numActive === 0) {
                log('  empty clause #'+gc.index+' (last lit killed by '+cell.id+'='+cell.value+')');
                return false; // contradiction: empty clause
            }
            if (gc.numActive === 1) {
                // Unit clause: find the remaining active literal and force it
                var forced = this.forceLiteral(gc);
                if (forced === false) {
                    return false; // contradiction
                }
                if (forced) {
                    queue.push(forced);
                }
            }
        }
        else if (gc.numActive === 1) {
            // Indeterminate but this is a unit clause: the function cell we
            // just assigned may have made the literal's terms fully ground.
            // Try to force it now.
            var forced = this.forceLiteral(gc);
            if (forced === false) {
                return false;
            }
            if (forced) {
                queue.push(forced);
            }
            else if (!cell.isFunction && lit.funcCellId) {
                // Cross-off: the triggering cell is a predicate cell and
                // this unit clause has a function term. The function cell
                // value that would resolve to this predicate cell is
                // cell.args[lit.funcArgPos]. If the clause polarity is
                // violated, eliminate that value.
                var violated = lit.positive ? (cell.value === false) : (cell.value === true);
                if (violated) {
                    var crossOff = this.eliminateValue(lit.funcCellId, cell.args[lit.funcArgPos], queue);
                    if (crossOff === false) return false;
                }
            }
        }
    }
    return true;
};

Model.prototype.evaluateLiteral = function(lit, occ) {
    /**
     * Evaluate a literal given current cell assignments.
     * Returns true if the literal is true, false if false, null if
     * indeterminate (some cells not yet assigned).
     *
     * If <occ> is provided ({clauseIdx, litIdx}), dynamically registers the
     * occurrence on any newly-discovered cell dependencies so that future
     * assignments to those cells will trigger re-evaluation.
     */
    var reducedTerms = this.reduceTermsFromCells(lit.terms);
    // Check if all terms are numbers:
    for (var i=0; i<reducedTerms.length; i++) {
        if (typeof reducedTerms[i] !== 'number') {
            // Register on any newly-revealed cell dependencies:
            if (occ) this.registerNewDependencies(reducedTerms, occ);
            return null;
        }
    }

    // Special case: equality
    if (lit.predicate === '=') {
        var atomVal = (reducedTerms[0] === reducedTerms[1]);
        return lit.positive ? atomVal : !atomVal;
    }

    var predCellId = lit.predicate + reducedTerms.toString();
    var predCell = this.cellIndex[predCellId];
    if (!predCell) {
        return null;
    }
    if (predCell.value === null) {
        // Register on the predicate cell so we're notified when it's assigned:
        if (occ) {
            // Check for same-clause duplicate: another active literal in this
            // ground clause whose terms currently reduce to the same predCell.
            // Two same-polarity literals targeting the same cell are redundant
            // (deactivate this one); opposite polarities make the clause a
            // tautology. This happens, e.g., when a function cell assignment
            // causes [¬Lf(v,u)u, ¬Lf(v,u)y, ¬Lyv] at (0,0,0) to collapse into
            // three copies of ¬L[0,0]. Without this check, the clause would
            // stay at numActive=3 until L[0,0] is branched on.
            var dup = this.checkSameClauseDedup(predCell, occ, lit.positive, predCellId);
            if (dup !== null) return dup;
            this.registerOccurrence(predCell, occ);
        }
        return null;
    }
    return lit.positive ? predCell.value : !predCell.value;
};

Model.prototype.checkSameClauseDedup = function(predCell, occ, litPositive, predCellId) {
    /**
     * Look for another active literal in the same clause as <occ> whose terms
     * currently reduce to <predCell>. Return true (caller should treat the
     * current literal as true — clause becomes a tautology), false (current
     * literal is redundant — deactivate it), or null (no duplicate).
     *
     * Occurrences are never removed on backtrack, so entries can be stale;
     * we re-verify the candidate's terms still reduce to <predCellId>.
     */
    for (var k=0; k<predCell.occurrences.length; k++) {
        var other = predCell.occurrences[k];
        if (other.clauseIdx !== occ.clauseIdx) continue;
        if (other.litIdx === occ.litIdx) continue;
        var otherLit = this.groundClauses[other.clauseIdx].literals[other.litIdx];
        if (!otherLit.active) continue;
        var otherReduced = this.reduceTermsFromCells(otherLit.terms);
        var allGround = true;
        for (var i=0; i<otherReduced.length; i++) {
            if (typeof otherReduced[i] !== 'number') { allGround = false; break; }
        }
        if (!allGround) continue;
        if (otherLit.predicate + otherReduced.toString() !== predCellId) continue;
        return (otherLit.positive === litPositive) ? false : true;
    }
    return null;
};

Model.prototype.registerNewDependencies = function(reducedTerms, occ) {
    /**
     * After partial reduction, register the occurrence on any function/constant
     * cells that appear as unresolved subterms in <reducedTerms>.
     */
    for (var i=0; i<reducedTerms.length; i++) {
        this.registerTermDependencies(reducedTerms[i], occ);
    }
};

Model.prototype.registerTermDependencies = function(term, occ) {
    if (typeof term === 'number') return;
    if (term.isArray) {
        // Function term like [f, 0, 1] — check if this cell exists and is
        // unassigned; also recurse into non-ground arguments:
        var allArgsGround = true;
        for (var i=1; i<term.length; i++) {
            if (typeof term[i] !== 'number') {
                allArgsGround = false;
                this.registerTermDependencies(term[i], occ);
            }
        }
        if (allArgsGround) {
            var cellId = term.toString();
            var cell = this.cellIndex[cellId];
            if (cell) {
                this.registerOccurrence(cell, occ);
            }
        }
    }
    else {
        // Constant string — register on it if it's a cell:
        var cell = this.cellIndex[term];
        if (cell) {
            this.registerOccurrence(cell, occ);
        }
    }
};

Model.prototype.liveOccurrences = function(cell) {
    /**
     * Return the number of occurrences of <cell> that can still matter: those
     * in a clause that isn't satisfied yet, on a literal that is still active.
     *
     * cell.occurrences is not a good measure by itself. Occurrences are added
     * as term dependencies are discovered and are deliberately kept on
     * backtracking (literals are re-evaluated, so keeping them is safe), which
     * means the list also holds entries that no longer say anything about the
     * current state.
     */
    var n = 0;
    for (var i=0; i<cell.occurrences.length; i++) {
        var occ = cell.occurrences[i];
        var gc = this.groundClauses[occ.clauseIdx];
        if (gc.satisfied) continue;
        if (!gc.literals[occ.litIdx].active) continue;
        n++;
    }
    return n;
};

Model.prototype.registerOccurrence = function(cell, occ) {
    /**
     * Add <occ> to cell's occurrence list if not already present.
     */
    var key = occ.clauseIdx + ':' + occ.litIdx;
    if (cell.occurrenceKeys.has(key)) return;
    cell.occurrenceKeys.add(key);
    cell.occurrences.push(occ);
};

Model.prototype.eliminateValue = function(funcCellId, value, queue) {
    /**
     * Eliminate <value> from the possible values of a function cell
     *
     * This is used when a unit clause like P(f(0)) forces P to be true at
     * every domain element, and we discover that P(k) is false for some k:
     * then f(0) cannot be k, so we eliminate k from f(0)'s possible values.
     *
     * If only one value remains after elimination, push a forced assignment
     * to <queue>. Returns false if no values remain (contradiction).
     */
    var funcCell = this.cellIndex[funcCellId];
    if (!funcCell || funcCell.value !== null) return null;
    var idx = funcCell.possible.indexOf(value);
    if (idx < 0) return null; // already eliminated
    this.trail.push({type: 'eliminate', cell: funcCell, value: value});
    funcCell.possible.splice(idx, 1);
    log('  eliminated '+value+' from '+funcCellId+' (now '+funcCell.possible.length+' value(s) left)');
    if (funcCell.possible.length === 0) {
        log('  '+funcCellId+' has no possible values');
        return false; // contradiction: no values left
    }
    if (funcCell.possible.length === 1) {
        queue.push({cell: funcCell, value: funcCell.possible[0]});
    }
    return null;
};

Model.prototype.forceLiteral = function(gc) {
    /**
     * Given a unit ground clause, determine what cell assignment is forced.
     *
     * Returns {cell, value} if a cell can be forced, false if the forced
     * value contradicts the cell's current assignment, or null if the
     * literal's terms contain unresolved function subterms (in which case we
     * register dependencies so we'll be notified when those cells are
     * assigned).
     */
    // Find the sole active literal:
    var lit = null;
    var litIdx = -1;
    for (var i=0; i<gc.literals.length; i++) {
        if (gc.literals[i].active) {
            lit = gc.literals[i];
            litIdx = i;
            break;
        }
    }
    if (!lit) return false; // shouldn't happen

    // Reduce terms:
    var occ = {clauseIdx: gc.index, litIdx: litIdx};
    var reducedTerms = this.reduceTermsFromCells(lit.terms);

    // Equality atoms are pre-assigned (not cells we can assign to), but a
    // positive unit equality where one side is a domain element and the other
    // is a fully-reduced function cell CAN force that cell.
    if (lit.predicate === '=') {
        var a = reducedTerms[0], b = reducedTerms[1];
        var aNum = typeof a === 'number', bNum = typeof b === 'number';
        if (aNum && bNum) {
            if (lit.positive === (a === b)) {
                // Already satisfied — mark clause satisfied
                this.trail.push({type: 'satisfy', clause: gc});
                gc.satisfied = true;
                return null;
            }
            return false; // contradiction
        }
        if (lit.positive && (aNum || bNum)) {
            var cellSide = aNum ? b : a, val = aNum ? a : b;
            var ground = cellSide.isArray;
            for (var i=1; ground && i<cellSide.length; i++) {
                if (typeof cellSide[i] !== 'number') ground = false;
            }
            var fcell = ground && this.cellIndex[cellSide.toString()];
            if (fcell && fcell.isFunction) {
                if (fcell.value === val) {
                    this.trail.push({type: 'satisfy', clause: gc});
                    gc.satisfied = true;
                    return null;
                }
                if (fcell.value !== null) return false;  // assigned differently
                if (fcell.possible.indexOf(val) === -1) return false;
                return {cell: fcell, value: val};
            }
        }
        this.registerNewDependencies(reducedTerms, occ);
        return null;
    }

    // Non-equality predicate: all terms must reduce to numbers to evaluate.
    for (var i=0; i<reducedTerms.length; i++) {
        if (typeof reducedTerms[i] !== 'number') {
            // Some function subterm not yet assigned. Register on the
            // newly-revealed dependencies so we're notified later.
            this.registerNewDependencies(reducedTerms, occ);
            return null;
        }
    }

    var predCellId = lit.predicate + reducedTerms.toString();
    var predCell = this.cellIndex[predCellId];
    if (!predCell) return null;

    var forcedValue = lit.positive; // true or false

    if (predCell.value !== null) {
        // Already assigned: check consistency
        if (predCell.value === forcedValue) {
            // Already satisfied
            this.trail.push({type: 'satisfy', clause: gc});
            gc.satisfied = true;
            return null;
        }
        return false; // contradiction
    }

    return {cell: predCell, value: forcedValue};
};

Model.prototype.selectCell = function() {
    /**
     * Select the next unassigned cell to branch on.
     *
     * Heuristic: function cells are tried before predicate cells, because
     * assigning a function cell (e.g. f(0) = 1) resolves function subterms in
     * many clauses, which often makes predicate literals evaluable and triggers
     * cascading propagation. Indeed, while f(0) is unassigned, P(f(0)) doesn't
     * refer to any one of P[0], P[1], .., so assigning predicate cells can't
     * simplify it at all. Within the same category, we prefer cells with fewer
     * remaining values.
     */
    var best = null;
    var bestIsFunc = false;
    var bestValues = Infinity;
    var bestMaxIndex = Infinity;
    for (var i=0; i<this.cells.length; i++) {
        var cell = this.cells[i];
        if (cell.fixed) continue;
        if (cell.value !== null) continue;
        if (this.liveOccurrences(cell) === 0) continue; // nothing left to decide
        var nv = cell.possible.length;
        var isFunc = cell.isFunction;
        // Prefer function cells; within same category, prefer fewer values:
        if ((isFunc && !bestIsFunc) || (isFunc === bestIsFunc && (nv < bestValues || (nv === bestValues && cell.maxIndex < bestMaxIndex)))) {
            best = cell;
            bestIsFunc = isFunc;
            bestValues = nv;
            bestMaxIndex = cell.maxIndex;
        }
    }
    return best;
};

Model.prototype.getCellValues = function(cell) {
    /**
     * Return the list of values to try for <cell>.
     *
     * For function terms, we exploit the fact that domain elements are
     * interchangeable. We can restrict each function cell to values at most one
     * beyond the highest domain element already used.     *
     */
    if (!cell.isFunction) {
        return cell.possible.slice();
    }
    // Function cell
    var termStr = cell.id; // e.g. 'a' or '[f,0,1]'
    var term = cell.args.length > 0 ? [cell.symbol].concat(cell.args) : cell.symbol;
    var maxValue = this.getMaxValue(term, termStr);
    var values = [];
    for (var i=0; i<cell.possible.length; i++) {
        if (cell.possible[i] <= maxValue) {
            values.push(cell.possible[i]);
        }
    }
    return values;
};

Model.prototype.buildInterpretation = function() {
    /**
     * Populate this.interpretation from cell values, in the format expected
     * by getExtensions().
     */
    this.interpretation = {};
    for (var i=0; i<this.cells.length; i++) {
        var cell = this.cells[i];
        if (cell.fixed) continue;
        if (cell.value !== null) {
            this.interpretation[cell.id] = cell.value;
        }
    }
};

Model.prototype.checkModel = function() {
    /**
     * Throw if the model we are about to report doesn't satisfy the ground clauses.
     */
    if (!this.verifyModel()) {
        throw new Error('internal error: the model found does not satisfy all ground clauses');
    }
};

Model.prototype.verifyModel = function() {
    /**
     * Check that all ground clauses are satisfied by the current cell
     * assignments. Returns true if the model is valid, false otherwise.
     */
    var mark = this.trail.length;
    for (var i=0; i<this.cells.length; i++) {
        var cell = this.cells[i];
        if (cell.fixed || cell.value !== null) continue;
        this.trail.push({type: 'assign', cell: cell, oldPossible: cell.possible});
        cell.value = cell.possible.length > 0 ? cell.possible[0]
            : (cell.isFunction ? 0 : false);
    }
    var res = this.allClausesSatisfied();
    this.undoToMark(mark);
    return res;
};

Model.prototype.allClausesSatisfied = function() {
    for (var ci=0; ci<this.groundClauses.length; ci++) {
        var gc = this.groundClauses[ci];
        var satisfied = false;
        for (var li=0; li<gc.literals.length; li++) {
            var tv = this.evaluateLiteral(gc.literals[li]);
            if (tv === true) {
                satisfied = true;
                break;
            }
        }
        if (!satisfied) {
            log('clause '+ci+' not satisfied');
            return false;
        }
    }
    return true;
};

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
        else sym = this.modelfinder.numericConstRestore[sym] || sym;
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
    var extByArgs = new Map();
    for (var i=0; i<extension.length; i++) {
        extByArgs.set(extension[i].slice(0,-1).join(','), extension[i]);
    }
    var res = [];
    do {
        var entry = extByArgs.get(args.join(','));
        res.push(entry || args.concat([0]));
    } while (Model.iterateTuple(args, maxValues));
    return res;
}

Model.prototype.toString = function() {
    /**
     * return string representation of model, for debugging
     */
    return this.toHTML().replace(/<.+?>/g, '');
}

Model.prototype.unassignedCount = function() {
    /**
     * Count cells still up for branching, for debugging
     */
    var n = 0;
    for (var i=0; i<this.cells.length; i++) {
        var c = this.cells[i];
        if (!c.fixed && c.value === null && c.occurrences.length > 0) n++;
    }
    return n;
};

Model.prototype.activeClauseCount = function() {
    /**
     * Count active clauses, for debugging
     */
    var n = 0;
    for (var i=0; i<this.groundClauses.length; i++) {
        if (!this.groundClauses[i].satisfied) n++;
    }
    return n;
};
