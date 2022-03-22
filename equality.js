/**
 * Here we define some methods for handling equality (identity).
 *
 * Most textbooks use two special rules, going back to Jeffrey: "Leibniz' Law"
 * (LL) and a closure rule (Ref) that allows closing any branch that contains
 * ¬(t=t).
 *
 * Unrestricted, (LL) opens up a huge search space. One can restrict the rule to
 * literals and constrain it so that it (1) only replaces "larger" terms by
 * "smaller" terms, relative to some ordering, and also (2) only replaces the
 * "larger" side of an equation. One can also delay application until some
 * sequence of applications allows closing a branch.
 *
 * In free-variable tableaux, Jeffrey's rules are incomplete: sometimes (LL)
 * must be applied simultaneously with a substitution of free variables. That
 * is, we need to check if there is some substitution under which some
 * applications of (LL) and (Ref) allow closing the current branch.
 *
 * For example, if the branch contains the equation E = { f(a)=b } as well as
 * the literals Pf(a)y and ¬Pxg(b), then we are looking for a substitution σ
 * under which E entails (f(a)=x)σ and (y=g(b))σ by LL. Finding such a
 * substitution is known as a rigid E-unification problem.
 * 
 * We use a simplified form of the E-unification calculus "BSE" suggested by
 * Degtyarev and Voronkov 1998 ("What you always wanted to know about rigid
 * E-unification"), partly following Franssen 2008 ("Implementing rigid
 * E-unification") for implementation details.
 *
 * The BSE calculus respects the idea that applications of (LL) should replace
 * larger terms by smaller terms. Unfortunately, we sometimes don't know at the
 * time when we want to apply (LL) -- say, replacing f(a) by x -- whether the
 * application meets the complexity-reducing condition, since the variable x
 * might only be instantiated later in the computation (or indeed only when
 * dealing with another branch). The BSE calculus therefore operates with
 * /constraints/ on possible substitutions.
 *
 * Constraints involve two kinds of conditions: equality conditions saying that
 * a substitution σ must render two terms s and t identical, and inequality
 * conditions saying that σ must render one term s "smaller" than another term
 * t. We interpret the smaller relation in terms of Lexicographic Path Ordering.
 * 
 * D&V describe a sound and complete tableau algorithm in which no substitution
 * is ever applied; instead, a tableaux is closed if the union of the
 * constraints that would allow closing each individual branch is non-empty. We
 * use a different approach. When working on a branch, we regularly check if one
 * of its E-unification problems can be solved. We collect all these solutions,
 * apply the substitution determined by the equality conditions of the first and
 * store the others for backtracking. (We forget the ordering constraint.)
 *
 */

function EqualityProblem(equationNodes) {
    /**
     * An EqualityProblem represents a rigid E-unification problem with a
     * constraint on substitutions. The goal of a rigid E-unification problem is
     * to find a substitution (variables -> terms) under which the target
     * equalities terms1[i]=terms2[i] can be derived from the supplied equations
     * by LL.
     *
     * Calling this.nextStep() will call one of the RBS rules (basically, one
     * application of LL) in all possible ways and return a list of resulting
     * EqualityProblems. If some of these are solved, they will come first in the
     * list and have this.nextStep == null.
     *
     * In comments below, I'll sometimes represent a unification problem like
     * this:
     * 
     *    <equations> ⊢ <goal>, [<constraint>]
     *
     * I here use the tilde for equality and '=' for syntactic identity.
     * 
     */
    // the (goal) term lists we want to unify:
    this.terms1 = null;
    this.terms2 = null;
    // the nodes from which these terms come (to annotate LL applications):
    this.terms1Node = null;
    this.terms2Node = null;
    // the equations on the branch that we can use to apply LL (pairs of terms):
    this.equations = [];
    // the constraint on substitutions that we will construct:
    this.constraint = arguments[0] || new SubstitutionConstraint();
    // new Nodes that were added by applications of LL:
    this.newNodes = [];
    // the scheduled next rrbs rule:
    this.nextStep = this.start;
    // bookkepping for recursion:
    this.lastStep = null;
    this.lrbsIndex = -1;
}

EqualityProblem.prototype.init = function(equationNodes, goalNode1, goalNode2) {
    /**
     * initialise the problem based on the supplied nodes
     */
    this.equations = equationNodes;
    this.terms1Node = goalNode1;
    this.terms2Node = goalNode2;
    if (goalNode1 == goalNode2) { // target is an inequality
        this.terms1 = [goalNode1.formula.sub.terms[0]];
        this.terms2 = [goalNode1.formula.sub.terms[1]];
    }
    else if (goalNode1.formula.sub) {
        this.terms1 = goalNode1.formula.sub.terms;
        this.terms2 = goalNode2.formula.terms;
    }
    else {
        this.terms1 = goalNode1.formula.terms;
        this.terms2 = goalNode2.formula.sub.terms;
    }
}

EqualityProblem.prototype.addSkolemConstraints = function(terms) {
    for (var i=0; i<terms.length; i++) {
        if (!terms[i].isArray) continue;
        if (terms[i][0][0] == 'φ' || terms[i][0][0] == 'ω') {
            terms[i][0][0].isSkolemTerm = true;
            var fvs = getVariablesInTermList(terms[i]);
            for (var j=0; j<fvs.length; j++) {
                this.constraint.addGreater(terms[i], fvs[j]);
            }
        }
    }
}

function getVariablesInTermList(terms) {
    var res = [];
    var dupe = {};
    for (var i=0; i<terms.length; i++) {
        if (terms[i].isArray) {
            res.extendNoDuplicates(getVariablesInTermList(terms[i]));
        }
        else if ((terms[i][0] == 'ξ' || terms[i][0] == 'ζ') && !dupe[terms[i]]) {
            dupe[terms[i]] = true;
            res.push(terms[i]);
        }
    }
    return res;
}

EqualityProblem.prototype.start = function() {
    /**
     * try the first application of LL to the goal terms in all possible
     * ways; return a list of resulting problems, with any solved ones
     * coming first.
     */
    log("starting; trying rrbs");
    return this.tryRrbs();
}

EqualityProblem.prototype.tryRrbs = function() {
    /**
     * Go through all possible (single) applications of the rrbs rule; create a
     * new EqualityProblem for each result; return a list of these new problems,
     * with any solved ones coming first.
     *
     * 
     * The rrbs rule allows using one of the equations in the problem to modify
     * the goal:
     *
     *         [E, l~r ⊢ s1..si[p]..sn~t1..tn], [C]
     * (rrbs)  -------------------------------------------
     *         [E, l~r ⊢ s1..si[r]..sn~t1..tn], [C, l>r, si[p]>ti, l=p]
     * 
     * (This rule is adapted from D&V to handle term lists as s and t.)
     * 
     * We look for candidate equations l~r and subterms p for which the new
     * constraint is satisfiable. For each candidate, we create a copy of the
     * problem in which we apply the (rrbs) rule, thereby changing the goal
     * terms and the constraint and adding the relevant (LL) application to
     * newNodes. Then we call tryEr() to see if the new goal terms can be
     * unified. If yes, we add the solved problem to the start of the returned
     * array. If no, we schedule another call of tryRrbs() for the newly created
     * problem in order to change another subterm of the (altered) goal terms,
     * etc. To the end of the schedule, we append a call of tryLrbs() on the
     * original problem, in order to change the equations.
     */

    // This function can be scheduled from itself or from tryLrbs(). If it is
    // scheduled from tryLrbs(), we have already tried all equations except
    // for the one that was altered by tryLrbs():
    var equations = this.lastStep == this.tryLrbs ?
        [this.equations[this.lrbsIndex]] : this.equations;

    log('# trying rrbs');
    
    // Instead of recursively calling other applications of rrbs or lrbs, we
    // collect these recursive calls in a list, which we return (so that the
    // browser can take a break in between calls):
    var schedule = []; 

    // We have a choice of which equation in which direction to use as l=r,
    // which goal term list (terms1 or terms2) to use as s or t, which
    // position to use as i, and which subterm p to replace in si. We
    // begin by looping over the goal term position i:
    for (var i=0; i<this.terms1.length; i++) {
        
        // don't need to do anything if s[i] is already identical to t[i]:
        log("checking if candidate terms "+this.terms1[i]+" and "+this.terms2[i]+" can be unified");
        var nc = this.constraint.tryAddEqual(this.terms1[i], this.terms2[i]);
        if (nc && nc == this.constraint) {
            // don't continue merely because nc exists; see commit from 15/07/21
            log("terms are already equal");
            continue;
        }

        // loop over both directions of the selected goal terms:
        for (var sIsTerms1=1; sIsTerms1>=0; sIsTerms1--) {
            var s = sIsTerms1 ? this.terms1 : this.terms2;
            var t = sIsTerms1 ? this.terms2 : this.terms1;
            
            log('trying rrbs with '+s[i]+' as si and '+t[i]+' as ti');
        
            // rrbs can only be applied if the constraint is compatible with si>ti:
            var fconstraint = this.constraint.tryAddGreater(s[i],t[i]);
            if (!fconstraint) continue;
            // NB: fconstraint is now an extended copy of this.constraint

            // collect all non-variable subterms of si as candidates for p
            // (variables are excluded by condition (3) on p.53 of D&V):
            var siSubterms = subterms(s[i]);

            // try each eligible equation, in both directions:
            for (var ei=0; ei<equations.length; ei++) {
                for (var lIsLHS=1; lIsLHS>=0; lIsLHS--) {
                    var l = equations[ei].formula.terms[lIsLHS ? 0 : 1];
                    var r = equations[ei].formula.terms[lIsLHS];
                    log('  trying '+l+' as l and '+r+' as r');

                    // rrbs can only be applied if constraint is compatible with l>r:
                    var sconstraint = fconstraint.tryAddGreater(l,r);
                    if (!sconstraint) continue;

                    // try all subterms of si as candidates for p:
                    for (var j=0; j<siSubterms.length; j++) {
                        var p = siSubterms[j];
                        log('  trying '+p+' as p');

                        // rrbs can only be applied if constraint is compatible with l=p:
                        var tconstraint = sconstraint.tryAddEqual(l,p)
                        if (!tconstraint) continue;
                        
                        // All requirements are met: we can apply the rule. I.e., we
                        // can replace one occurrence of p in si by r, using (LL). We
                        // go through all occurrences.
                        var new_sis = replaceSubterm(s[i], p, r);
                        for (var g=0; g<new_sis.length; g++) {
                            log('rrbs constraints satisfied: replacing '+s[i]+' by '+new_sis[g]);
                            var newProblem = this.copy(tconstraint);
                            newProblem.applyLLtoGoal(i, sIsTerms1, new_sis[g], equations[ei]);
                            newProblem.lastStep = this.tryRrbs;
                            log('scheduling new problem '+newProblem+'; checking if solved by er');
                            // check if resulting problem can be solved directly: 
                            if (newProblem.tryEr()) {
                                log("yes, add to start of schedule");
                                newProblem.nextStep = null;
                                schedule.unshift(newProblem);
                            }
                            // schedule unsolved problem for further processing:
                            else {
                                log("no, add to end of schedule");
                                newProblem.nextStep = this.tryRrbs;
                                schedule.push(newProblem);
                            }
                            log('continuing with rrbs application to '+this);
                        }
                    }
                }
            }
        }
    }
    log("scheduling same problem with lrbs");
    this.nextStep = this.tryLrbs;
    schedule.push(this);
    return schedule.removeDuplicates();
}
 
EqualityProblem.prototype.tryLrbs = function() {
    /**
     * Go through all possible (single) applications of the lrbs rule; create a
     * new EqualityProblem for each result; return a list of these new problems.
     * 
     * The lrbs rule allows using one of the equations to modify another equation:
     *
     *         [E, l~r, s[p]~t ⊢ e], [C]
     * (lbrs)  -------------------------------------------
     *         [E, l~r, s[r]~t ⊢ e], [C, l>r, s[p]>t, l=p]
     *
     * We look for candidate equations l~r and subterms p for which the new
     * constraint is satisfiable. (If there is none, this path of the search is
     * a dead end, and we return an empty list.)
     *
     * For each candidate, we create a copy of the problem in which we apply the
     * (lrbs) rule, changing an equation and the constraint and adding the
     * relevant (LL) application to newNodes. Then we schedule a call to tryRrbs
     * to check if the new equation allows unifying the goal terms. (tryRrbs()
     * will schedule another call of this function to modify another equation,
     * etc.)
     */
    
    log('# trying lrbs');

    var schedule = [];
    
    // We need to choose two equations: l~r and s~t. So we loop twice over the
    // equations. Each equation has to be considered in both directions. (The
    // counters 'j' and 'i' are used like in Franssen 2008.
    for (var j=0; j<this.equations.length; j++) {
        for (var sIsLHS=1; sIsLHS>=0; sIsLHS--) {
            var s = this.equations[j].formula.terms[sIsLHS ? 0 : 1];
            var t = this.equations[j].formula.terms[sIsLHS];
            log('trying lrbs with '+s+' as s and '+t+' as t');
            
            // lrbs can only be applied if constraint is compatible with s>t:
            var fconstraint = this.constraint.tryAddGreater(s,t);
            if (!fconstraint) continue;

            // After finding a candidate for applying lrbs, we call tryRrbs(),
            // which will probably change the goal terms and then call this
            // function again, to make further changes to the equations. In that
            // case, we don't want to loop over all the equations again.
            // Instead, if the previous candidate had equation j as the target
            // s~t, we only need to re-try equations before j as targets for
            // the source equation l~r that was changed in the last call, i.e.
            // that was the target of the previous equation. We store this index
            // j in this.lrbsIndex.
            var sourceEquations = (j <= this.lrbsIndex) ?
                [this.equations[this.lrbsIndex]] : this.equations;
            for (var i=0; i<sourceEquations.length; i++) {
                for (var lIsLHS=1; lIsLHS>=0; lIsLHS--) {
                    var l = sourceEquations[i].formula.terms[lIsLHS ? 0 : 1];
                    var r = sourceEquations[i].formula.terms[lIsLHS];
                    log('   trying '+l+' as l and '+r+' as r');

                    // also need l>r:
                    var sconstraint = fconstraint.tryAddGreater(l,r);
                    if (!sconstraint) continue;

                    // try all subterms of s as candidates for p:
                    var sSubterms = subterms(s);
                    for (var k=0; k<sSubterms.length; k++) {
                        var p = sSubterms[k];
                        log('  trying '+p+' as p');

                        // lrbs can only be applied if constraint is compatible with l=p:
                        var tconstraint = sconstraint.tryAddEqual(l,p);
                        if (!tconstraint) continue;

                        // All requirements are met: we can apply the rule. I.e., we
                        // can replace one occurrence of p in s by r, using (LL). We
                        // try all occurrences.
                        var new_ss = replaceSubterm(s, p, r); 
                        for (var g=0; g<new_ss.length; g++) {
                            var new_s = new_ss[g];
                            // don't apply rule if new_s = t (D&V, condition (4), p.53):
                            if (new_s.toString() == t.toString()) continue;
                            log('lrbs constraints satisfied: replacing s[p]='+s+' by s[r]='+new_ss[g]);
                            var newProblem = this.copy(tconstraint);
                            newProblem.applyLLtoEquation(j, sIsLHS, new_ss[g], sourceEquations[i]);
                            newProblem.lrbsIndex = j;
                            newProblem.lastStep = newProblem.tryLrbs;
                            newProblem.nextStep = newProblem.tryRrbs;
                            log('scheduling new problem '+newProblem);
                            schedule.push(newProblem);
                        }
                    }
                }
            }
        }
    }
    return schedule.removeDuplicates(); 
}

EqualityProblem.prototype.tryEr = function() {
    /**
     * try unification of goal terms
     */
    log("# trying er()");
    var con = this.constraint;
    for (var i=0; i<this.terms1.length; i++) {
        con = con.tryAddEqual(this.terms1[i], this.terms2[i]);
        if (!con) return false;
    }
    // We're done. Any substitution that meets con renders terms1 and terms2
    // identical, which allows closing the branch.
    this.constraint = con;
    log("solved: "+this);
    return true;
}

EqualityProblem.prototype.applyLLtoGoal = function(i, sIsTerms1, new_si, equation) {
    /**
     * Apply a hypothetical (post-substitution) instance of LL to current
     * problem in which one term si (at index <i>) of the goal term list s is
     * replaced by <new_si>, based on <equation>. If <sIsTerms1> is 1, the goal
     * term list s is this.terms1, otherwise it is this.terms2.
     */
    if (sIsTerms1) {
        log("LL: replacing "+this.terms1[i]+" in "+this.terms1Node+" by "+new_si); 
        this.terms1 = this.terms1.copy();
        this.terms1.splice(i, 1, new_si);
    }
    else {
        log("LL: replacing "+this.terms2[i]+" in "+this.terms2Node+" by "+new_si); 
        this.terms2 = this.terms2.copy();
        this.terms2.splice(i, 1, new_si);
    }
    if (this.terms1Node == this.terms2Node) {
        // LL applied to one side of the inequality terms1Node (= terms2Node)
        var newFormula = new AtomicFormula('=', [this.terms1[0], this.terms2[0]]).negate();
        var newNode = new Node(newFormula,
                               Prover.equalityReasoner, // fromRule
                               [equation, this.terms1Node] // fromNodes
                              );
        this.newNodes.push(newNode);
        this.terms1Node = newNode;
        this.terms2Node = newNode;
    }
    else {
        // LL applied to terms1Node if sIsTerms1 else to terms2Node
        var targetNode = sIsTerms1 ? this.terms1Node : this.terms2Node;
        var targetAtom = targetNode.formula.sub || targetNode.formula;
        var newFormula = new AtomicFormula(targetAtom.predicate,
                                           sIsTerms1 ? this.terms1 : this.terms2);
        if (targetNode.formula.sub) newFormula = newFormula.negate();
        var newNode = new Node(newFormula,
                               Prover.equalityReasoner,
                               [equation, targetNode]
                              );
        this.newNodes.push(newNode);
        if (sIsTerms1) this.terms1Node = newNode;
        else this.terms2Node = newNode;
    }
}

EqualityProblem.prototype.applyLLtoEquation = function(j, sIsLHS, new_s, sourceEq) {
    /**
     * Apply a hypothetical (post-substitution) instance of LL to current
     * problem in which a term s in this.equations[j] is replaced by <new_s>,
     * based on <equation>. If <sIsLHS> is 1, the term s is the LHS of the
     * target equation, otherwise it is the RHS.
     */
    var targetEq = this.equations[j];
    var newFormula = new AtomicFormula('=', [
        sIsLHS ? new_s : targetEq.formula.terms[0],
        sIsLHS ? targetEq.formula.terms[1] : new_s
    ]);
    var newNode = new Node(newFormula,
                           Prover.equalityReasoner, // fromRule
                           [sourceEq, targetEq] // fromNodes
                          );
    this.newNodes.push(newNode);
    this.equations = this.equations.copy();
    this.equations.splice(j, 1, newNode);
}

EqualityProblem.prototype.getSubstitution = function() {
    /**
     * return a substition compatible with this.constraint, for applying to the
     * tree once a solution is found
     */
    var sdict = this.constraint.solvedForms[0].solvedDict;
    var res = [];
    for (var v1 in sdict) {
        res.push(v1, sdict[v1]);
    }
    return res;
}

EqualityProblem.prototype.copy = function(constraint) {
    var res = new EqualityProblem(constraint || this.constraint);
    res.terms1 = this.terms1; // don't need to copy because the array is never changed, only replaced (see applyLL functions)
    res.terms2 = this.terms2; // same
    res.equations = this.equations; // same
    res.terms1Node = this.terms1Node;
    res.terms2Node = this.terms2Node;
    res.newNodes = this.newNodes.copy();
    res.lastStep = this.lastStep;
    res.nextStep = this.nextStep;
    res.lrbsIndex = this.lrbsIndex;
    return res;
}

EqualityProblem.prototype.toString = function() {
    var nextStepStr = this.nextStep==this.tryRrbs ? 'rrbs' :
        this.nextStep==this.tryLrbs ? 'lrbs' :
        this.nextStep==this.tryEr ? 'er' :
        this.nextStep==this.start ? 'start' :
        this.nextStep==null ? '' : '???';
    return '&lt;' + this.equations + ' ⊢ ' + this.terms1 + '=' + this.terms2
        + ' (' + this.constraint + ') *' + nextStepStr + '&gt;';
}

function subterms(term) {
    /**
     * return all (distinct) subterms of <term>, except for variables and subterms
     * within skolem terms
     *
     * We don't need to replace terms within skolem terms. However, we can't treat
     * skolem terms as completely atomic: if a skolem term contains variable x, we
     * can't susbstitute x for that term. This is automatically ensured by returning
     * the skolem term as a proper function term.
     */
    if (term.isArray) {
        if (term[0][0] == 'φ' || term[0][0] == 'ω') { // skolem term
            return [term];
        }
        var res = [term];
        for (var i=1; i<term.length; i++) { // skip function symbol
            res.extendNoDuplicates(subterms(term[i]));
        }
        return res;
    }
    if (term[0] == 'ξ' || term[0] == 'ζ') return [];
    return [term];
}

function replaceSubterm(term, sub, repl) {
    /**
     * return list of all terms that result from <term> by replacing one occurrence
     * of <sub> with <repl>; ignore occurrences within skolem terms
     */
    var subStr = sub.toString();
    if (term.toString() == subStr) return [repl];
    if (!term.isArray || term[0][0] == 'φ' || term[0][0] == 'ω') return [];
    var res = [];
    for (var i=1; i<term.length; i++) {
        var newSubterms = replaceSubterm(term[i], sub, repl);
        for (var j=0; j<newSubterms.length; j++) {
            var newTerm = term.copy()
            newTerm.splice(i, 1, newSubterms[j]);
            res.push(newTerm);
        }
    }
    return res;
}


/**
 *
 * In order to check satisfiability of a constraint, we rewrite the constraint
 * into a disjunction of "solved forms". A solved form makes explicit all ordering
 * and equality conditions that are implied by a constraint.
 * 
 */

function SubstitutionConstraint(equalities, inequalities, solvedForms) {
    this.equalities = equalities || [];
    this.inequalities = inequalities || [];
    // The above two properties are only used for debugging/bookkeeping,
    // what matters is the next one.
    this.solvedForms = solvedForms || [new SolvedForm()];
}

SubstitutionConstraint.prototype.tryAddEqual = function(s, t) {
    /**
     * check if the syntactic identity s=t is compatible with the present
     * constraint; if yes, return a new constraint with the added condition (or
     * the same constraint if the condition is already entailed); if no, return
     * null.
     */
    var sfChanged = false;
    var sfs = [];
    for (var i=0; i<this.solvedForms.length; i++) {
        var sf = this.solvedForms[i].addEqual(s,t);
        if (sf.length != 1 || !sf[0].equals(this.solvedForms[i])) sfChanged = true;
        sfs.extendNoDuplicates(sf);
    }
    if (sfs.length == 0) {
        log("   can't add "+s+"="+t+" to constraint "+this.solvedForms);
        return null;
    }
    if (sfChanged) {
        log("   OK, can add "+s+"="+t+" to constraint "+this.solvedForms+" => "+sfs);
        var newEqualities = this.equalities.copy();
        newEqualities.push(s+'='+t);
        // newEqualities.push([s,t]);
        return new SubstitutionConstraint(newEqualities, this.inequalities, sfs);
    }
    else {
        log("   "+s+"="+t+" is already entailed by "+this.solvedForms);
        return this;
    }
}

SubstitutionConstraint.prototype.tryAddGreater = function(s, t) {
    /**
     * check if s>t is compatible with the present constraint; if yes, return a
     * new constraint with the added condition (or the same constraint if the
     * condition is already entailed); if no, return null. 
     */
    var sfChanged = false;
    var sfs = [];
    for (var i=0; i<this.solvedForms.length; i++) {
        var sfa = this.solvedForms[i].addGreater(s,t);
        if (sfa.length != 1 || !sfa[0].equals(this.solvedForms[i])) sfChanged = true;
        sfs.extendNoDuplicates(sfa);
    }
    if (sfs.length == 0) {
        log("   can't add "+s+">"+t+" to constraint "+this.solvedForms);
        return null;
    }
    if (sfChanged) {
        log("   OK, can add "+s+">"+t+" to constraint "+this.solvedForms+" => "+sfs);
        var newInequalities = this.inequalities.copy();
        // newInequalities.push([s,t]);
        newInequalities.push(s+'>'+t);
        return new SubstitutionConstraint(this.equalities, newInequalities, sfs);
    }
    else {
        log("   "+s+">"+t+" is already entailed by "+this.solvedForms);
        return this;
    }
}

SubstitutionConstraint.prototype.toString = function() {
    // var res = [];
    // for (var i=0; i<this.equalities.length; i++) {
    //     res.push(this.equalities[i][0]+'='+this.equalities[i][1]);
    // }
    // for (var i=0; i<this.inequalities.length; i++) {
    //     res.push(this.inequalities[i][0]+'>'+this.inequalities[i][1]);
    // }
    // return res.join(' ');
    return this.equalities.join(' ')+' '+this.inequalities.join(' ');
}


function SolvedForm() {
    this.solvedDict = {}; // mapping v->t, represents that any solution must make
                          // variable v identical to t
    this.solvedDictStr = []; // the same mapping as list of strings 'v=t', in
                             // alphabetic order
    this.inequalities = []; // list of (s>t) term pairs, one side of which is a
                            // variable not in this.solvedDict
    this.inequalitiesStr = []; // the same list as strings 's>t', in alphabetic order
}

SolvedForm.prototype.addEqual = function(s, t) {
    /**
     * check if this SolvedForm can be extended by condition s=t; return
     * list of extended SolvedForms (might be empty list)
     */
    // apply known substitution to s and t:
    var sStr = s.toString();
    var tStr = t.toString();
    for (var v in this.solvedDict) {
        if (sStr.includes(v)) {
            s = Formula.substituteInTerm(s, v, this.solvedDict[v]);
            sStr = s.toString();
        }
        if (tStr.includes(v)) {
            t = Formula.substituteInTerm(t, v, this.solvedDict[v]);
            tStr = t.toString();
        }
    }
    if (sStr == tStr) {
        // constraint is trivial; nothing to add
        log("   [add "+s+"="+t+" to "+this+"?] trivial");
        return [this];
    }
    if (sStr[0] == 'ξ' || sStr[0] == 'ζ') { // s is variable
        // if (this.occursCheck(s,t)) {
        if (this.occursCheckStr(sStr,tStr)) {
            // s occurs in t; unification impossible
            log("   [add "+s+"="+t+" to "+this+"?] no, s occurs in t");
            return [];
        }
        else {
            // add equality between variable s and term t:
            return this.addSubs(s,t);
        }
    }
    else if (tStr[0] == 'ξ' || tStr[0] == 'ζ') { // t is variable
        return this.addEqual(t,s);
    }
    else if (s.isArray && t.isArray) { // both terms functional
        if (s[0] != t[0]) {
            // a substitution can't make g(...) identical to f(....)
            log("   [add "+s+"="+t+" to "+this+"?] no, different function terms");
            return [];
        }
        // add equality condition for all subterms:
        log("   [add "+s+"="+t+" to "+this+"?] checking identity for subterms");
        var res = [this];
        for (var i=1; i<s.length; i++) {
            // add s[i]=t[i] equality to all members of res:
            var newRes = [];
            for (var j=0; j<res.length; j++) {
                newRes.extendNoDuplicates(res[j].addEqual(s[i],t[i]));
            }
            res = newRes;
        }
        return res;
    }
    else return [];
}

SolvedForm.prototype.addSubs = function(v, t) {
    /**
     * return list of new SolvedForms with added substitution <v>-><t>;
     * apply substitution to equalities and inequalities
     */
    var sf = new SolvedForm();
    // first create new solvedDict;
    for (v2 in this.solvedDict) {
        sf.solvedDict[v2] = Formula.substituteInTerm(this.solvedDict[v2], v, t);
        sf.solvedDictStr.push(v2+'='+sf.solvedDict[v2]);
    }
    sf.solvedDict[v] = t;
    sf.solvedDictStr.push(v+'='+t);
    sf.solvedDictStr.sort();
    log("   [add "+v+"="+t+" to "+this+"?] substituting "+v+" by "+t+" in inequalities");
    var res = [sf];
    for (var i=0; i<this.inequalities.length; i++) {
        var ineq = this.inequalities[i];
        // add ineq[0]>ineq[1] to all members of res and set res to the union of
        // the results:
        var newRes = [];
        for (var j=0; j<res.length; j++) {
            newRes.extendNoDuplicates(res[j].addGreater(ineq[0],ineq[1]));
        }
        res = newRes;
    }
    log("   [add "+v+"="+t+" to "+this+"?] result: "+res);
    return res;
}

SolvedForm.prototype.addGreater = function(s, t) {
    /**
     * check if this SolvedForm can be extended by condition s>t; return
     * list of extended SolvedForms (might be empty list)
     */
    var sStr = s.toString();
    var tStr = t.toString();
    // apply known substitution to s and t:
    for (var v in this.solvedDict) {
        if (sStr.includes(v)) {
            s = Formula.substituteInTerm(s, v, this.solvedDict[v]);
            sStr = s.toString();
        }
        if (tStr.includes(v)) {
            t = Formula.substituteInTerm(t, v, this.solvedDict[v]);
            tStr = t.toString();
        }
    }
    var sIsVar = sStr[0] == 'ξ' || sStr[0] == 'ζ';
    var tIsVar = tStr[0] == 'ξ' || tStr[0] == 'ζ';
    if (sIsVar || tIsVar) {
        if (this.inequalitiesStr.includes(sStr+'>'+tStr)) {
            log("   [add "+s+">"+t+" to "+this+"?] yes, already part of constraint");
            return [this];
        }
        if (sIsVar && this.occursCheckStr(sStr,tStr)) {
            // if variable s occurs in t, we can't have s>t:
            log("   [add "+s+">"+t+" to "+this+"?] no, s occurs in t");
            return [];
        }
        else if (tIsVar && this.occursCheckStr(tStr,sStr)) {
            // if variable t occurs in s, we automatically have s>t:
            log("   [add "+s+">"+t+" to "+this+"?] yes, trivially: t occurs in s");
            return [this];
        }
        else {
            // we can't have s>t and also t>s:
            if (this.inequalitiesStr.includes(tStr+'>'+sStr)) {
                log("   [add "+s+">"+t+" to "+this+"?] no, clash with "+this.inequalities[i]);
                return [];
            }
            // create extended sf:
            var sf = this.copy();
            sf.inequalities.push([s,t]);
            sf.inequalitiesStr.push(sStr+'>'+tStr);
            sf.inequalities.sort(); // for comparing sfs
            // here we should ideally check sf.checkSatisfiable()
            log("   [add "+s+">"+t+" to "+this+"?] yes. extended sf is "+sf);
            return [sf];
        }
    }
    var sRoot = s.isArray ? s[0] : s;
    var tRoot = t.isArray ? t[0] : t;
    if (sRoot > tRoot) { // function symbol of s is "greater"
        // f(v1..vn) > g(u1..um); we add f(v1..vn) > u1, ..., f(v1...vn) > um;
        // each of these additions may return a set of SolvedForms.
        log("   [add "+s+">"+t+" to "+this+"?] function symbol of "+s+" is greater");
        var res = [this];
        if (t.isArray) {
            for (var i=1; i<t.length; i++) {
                // try to extend all members of res by s>t[i]; return union of the
                // results:
                var newRes = [];
                for (var j=0; j<res.length; j++) {
                    newRes.extendNoDuplicates(res[j].addGreater(s,t[i]));
                }
                res = newRes;
            }
            log("   [add "+s+">"+t+" to "+this+"?] result: "+res);
        }
        // here we should ideally filter by sf.checkSatisfiable()
        return res;
    }
    else if (tRoot > sRoot) { // function symbol of t is "greater"
        // f(v1..vn) > g(u1..um); we add v1 >= g(u1..um) OR .. OR vn >= g(u1..um)
        log("   [add "+s+">"+t+" to "+this+"?] function symbol in 2nd term is greater; one arg in 1st must be >= 1st term");
        var res = [];
        if (s.isArray) {
            for (var i=1; i<s.length; i++) {
                res.extendNoDuplicates(this.addEqual(s[i],t));
                res.extendNoDuplicates(this.addGreater(s[i],t));
            }
            log("   [add "+s+">"+t+" to "+this+"?] result: "+res);
        }
        // here we should ideally filter by sf.checkSatisfiable()
        return res;
    }
    else { // s and t have same function symbol
        // f(v1..vn) > f(u1..un); we add the following:
        // v1 >= f(u1..un) OR .. OR vn >= f(u1..un)
        // OR (v1 > u1, f(v1..vn) > u2, .., f(v1..vn) > un)
        // OR (v1 = u1, v2 > u2, f(v1..vn) > u3, .., f(v1..vn) > un)
        // ...
        // OR (v1 = u1, v2 = u2, .., vn > un)
        if (!s.isArray) {
            log("   [add "+s+">"+t+" to "+this+"?] no: same constant");
            return [];
        }
        var res = [];
        log("   [add "+s+">"+t+" to "+this+"?] same function symbol; f(..ti..)>f(..si..) if ti>=f(..si..)");
        for (var i=1; i<s.length; i++) { 
            res.extendNoDuplicates(this.addEqual(s[i],t));
            res.extendNoDuplicates(this.addGreater(s[i],t));
        }
        log("   ["+s+">"+t+"?] alternatively, f(..ti..)>f(..si..) if t1=s1,..,ti>si,f(..ti+j..)>si+j");
        var eq = [this];
        for (var i=1; i<s.length; i++) {
            // add s[i]>t[i] to all members of eq:
            var h = [];
            for (var j=0; j<eq.length; j++) {
                h.extendNoDuplicates(eq[j].addGreater(s[i], t[i], 1));
            }
            for (var j=i+1; j<s.length; j++) {
                // add s>t[j] to all members of h:
                var newH = [];
                for (var k=0; k<h.length; k++) {
                    newH.extendNoDuplicates(h[k].addGreater(s[i], t[i], 1));
                }
                h = newH;
            }
            res.extendNoDuplicates(h);
            // add s[i]=t[i] to all members of eq:
            var newEq = [];
            for (var j=0; j<eq.length; j++) {
                newEq.extendNoDuplicates(eq[j].addEqual(s[i], t[i], 1));
            }
            eq = newEq;
        }
        log("   ["+s+">"+t+"?] new sfs: "+res);
        // here we should ideally filter by sf.checkSatisfiable()
        return res;
    }
}

SolvedForm.prototype.occursCheck = function(v, t) {
    /**
     * check if variable v occurs in term t
     */
    if (t[0] == 'ξ' || t[0] == 'ζ') {
        // while (t in this.solvedDict) t = this.solvedDict[t];
        return t == v;
    }
    else if (t.isArray) {
        for (var i=1; i<t.length; i++) {
            if (this.occursCheck(v, t[i])) return true;
        }
    }
    return false;
}

SolvedForm.prototype.occursCheckStr = function(v, t) {
    /**
     * check if variable v occurs in term t
     */
    var ts = t.split(v, 2);
    if (ts.length == 2) {
        return isNaN(ts[1][0]);
    }
    return false;
}

SolvedForm.prototype.checkSatisfiable = function() {
    /**
     * Ideally, we should check if the ordering constraints in a solved form are
     * satisfiable. Franssen 2008 discusses some implementation ideas. In practice,
     * it hurts little to leave out this check: worst case we'll end up sometimes
     * substituting smaller terms by larger terms; this doesn't affect soundness
     * and shouldn't affect completeness given our breadth-first search.
     */
    return true;
}

SolvedForm.prototype.copy = function() {
    var res = new SolvedForm();
    for (key in this.solvedDict) {
        res.solvedDict[key] = this.solvedDict[key];
    }
    res.solvedDictStr = this.solvedDictStr.copy();
    res.inequalities = this.inequalities.copy();
    res.inequalitiesStr = this.inequalitiesStr.copy();
    return res;
}

SolvedForm.prototype.equals = function(sf) {
    if (this.solvedDictStr.join() != sf.solvedDictStr.join()) return false;
    return (this.inequalitiesStr.join() == sf.inequalitiesStr.join());
}

SolvedForm.prototype.toString = function() {
    return '{'+this.solvedDictStr.join(' ')+' '+this.inequalitiesStr.join(' ')+'}';
}
