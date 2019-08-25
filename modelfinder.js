// Often there are simple countermodels that are hard to find through the tree
// method; so we run a separate algorithm to find such countermodels.
//
// This works as follows.
//
// 1. We transform the formulas for which we want to find a model (in
//    demodalized NNF) into clausal normal form, which gives us literal
//    "constraints" that we're trying to satisfy. For example, Fa ∧ Fb is split
//    into two constraints, Fa and Fb; ∀x∃yRxy is turned into Rxf(x); Fa ∨ Fb is
//    turned into the disjunctive constraint [Fa, Fb].
//
// 2. Now we start with a domain of size 1, namely [0]. If no countermodel is
//    found, we increase the domain to [0,1], and so on. The interpretation of
//    terms and predicates is initially empty. For each domain choice, we do the
//    following:
//
// 3. We replace free variables in the constraints by numbers. So ∀xFx is
//    replaced by two constraints, F0 and F1. [Numerals in formulas are never
//    interpreted as terms, so there can be no clash.]
//
// 4. Now we go through all the constraints (which are lists of literals,
//    interpreted disjunctively). If a constraint contains uninterpreted terms,
//    we also go through all ways of assigning to them members of the domain as
//    referents. (We don't assign a full meaning to function symbols here, only
//    to complete terms like f(a,g(b)) and to their parts.) For each of these
//    assignments, we try to satisfy the constraint by extending the
//    interpretation of the predicates. (For example, if we need to satisfy F0,
//    we check if |F| is already defined for 0; if not, we set |F|(0)=true; if
//    |F| is defined and |F|(0)=true, we continue; if |F|(0)=false, we give up.)
//    Whenever the constraint is satisfied, we move on to the next
//    constraint. If satisfaction is impossible, we backtrack and try another
//    interpretation of the individuals.
//
// Models for originally modal formulas (which we recognize from parser.isModal
// == true) have two domains, W and D. The elements of W are also natural
// numbers starting with 0. (That's OK: nothing in the definition of a Kripke
// model requires that the worlds must be distinct from the individuals; note
// that we can still have more worlds than individuals or more individuals than
// worlds.) When breaking down initFormulas into constraints, we take into
// account which variables quantify over worlds and which over
// individuals. Accessibility conditions like reflexivity are added to the
// formulas for which we want to find a model. In modal models, all predicates
// take a world as their last argument; 'R' takes two worlds, function terms
// only take individuals.

function ModelFinder(initFormulas, parser, accessibilityConstraints, s5) {
    // initFormulas = list of demodalized formulas in NNF for which we try to
    //                find a model
    // accessibilityConstraints = another such list, for modal models
    log("*** creating ModelFinder");

    this.parser = parser;
    this.s5 = s5;
    
    if (s5) {
        accessibilityConstraints = [];
        initFormulas = initFormulas.map(function(f) {
            return parser.stripAccessibilityClauses(f);
        });
    }
    
    // collect expressions that need to be interpreted:
    this.predicates = parser.getSymbols('predicate');
    if (s5) this.predicates.remove(parser.R);
    this.constants = parser.getSymbols('individual constant');
    this.funcSymbols = parser.getSymbols('function symbol');
    if (parser.isModal) {
        log('adding w');
        this.constants.unshift(parser.w);
    }

    // break down initFormulas and accessibilityConstraints into clauses:
    initFormulas = initFormulas.concat(accessibilityConstraints || []);
    this.clauses = this.getClauses(initFormulas);

    // needed in Model.iterateDenotations():
    this.names = parser.getSymbols('individual constant'); // now includes skolem constants 
    this.worldNames = parser.getSymbols('world constant');
    this.isWorldTerm = {}; // set by Model.getConstraintTerms()

    // initialize model:
    var numIndividuals = 1;
    var numWorlds = this.parser.isModal ? 1 : 0;
    this.model = new Model(this, numIndividuals, numWorlds);
}

ModelFinder.prototype.getClauses = function(formulas) {
    // convert <formulas> into clausal normal form and return combined list of
    // clauses
    var res = [];
    for (var i=0; i<formulas.length; i++) {
        var formula = formulas[i]; 
        log('getting clauses from '+formula);
        var clauses = this.parser.clausalNormalForm(formula);
        res = res.concatNoDuplicates(clauses);
    }
    log('all clauses: '+res);
    res = this.simplifyClauses(res);
    log('simplified clauses: '+res);
    return res;
}

ModelFinder.prototype.simplifyClauses = function(clauseList) {
    // simplify <clauseList>

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
    // remove repetitions in clauses, as in [p,p,q]; also order each clause
    // alphabetically:
    var nl = nl.map(function(clause) {
        return clause.removeDuplicates().sort();
    });
    // sort clauses by length:
    nl.sort(function(a,b){ return a.length > b.length; });
    // If clause A is a subset of (or equal to) clause B, clause B can be
    // removed (e.g. [[p],[p,q]] => [[p]] or [[q,s],[p,q,r,s]] => [[q,s]]. The
    // naive way to test this is O(n!). We store which clauses contain which
    // literals: q => [c1,c2]...  For each clause, we intersect store[q] with
    // store[s]. This still takes too long if we have a lot of clauses.
    if (nl.length > 5000) return nl;
    nl2 = nl.copy();
    var literals2clauses = {};
    for (var i=0; i<nl.length; i++) {
        for (var k=0; k<nl[i].length; k++) {
            var lit = nl[i][k].string;
            if (!literals2clauses[lit]) literals2clauses[lit] = [nl[i]];
            else literals2clauses[lit].push(nl[i]);
        }
    }
    for (var i=0; i<nl.length; i++) {
        var clause = nl[i];
        var lit = clause[0].string;
        var supersets = literals2clauses[lit];
        // log(clause+': supsersets from first literal: '+supersets);
        for (var k=1; k<clause.length; k++) {
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
    // Each call of this function tries to satisfy one constraint, namely
    // model.constraints[model.constraintPosition]. We need to do slightly
    // different things depending on whether (a) we're processing this
    // constraint for the first time, (b) we're processing it again after having
    // processed it just before, or (c) we're processing it again after backtracking.
    //
    // In case (a), where we process the node for the first time, we (1) assign
    // to all new terms the denotation 0; then we (2) see if there's an
    // interpretation of the predicates that satisfies the constraint (there may
    // be several if the constraint is disjunctive); if yes, we move on to the
    // next constraint on the next call; if no, we try the same constraint
    // again.
    //
    // In case (b), where we process the same constraint again, we (1') try to
    // find a new assignment of denotations to the new terms; if there's none,
    // we backtrack to earlier constraints or increase the domain if there are
    // no earlier constraints; if there is a new assignment of terms, we go
    // through (2) as above.
    //
    // In case (c), where we've returned to the constraint through backtracking,
    // we (0) see if there's another interpretation of the predicates that
    // satisfies the constraint; if yes, we move on to the next constraint; if
    // no, we procede as in case (b).

    log("*** modelfinder"); 
    var model = this.model;
    var curConstraint = model.constraints[model.constraintPosition];
    var prevConstraintPosition = model.prevConstraintPosition;
    model.prevConstraintPosition = model.constraintPosition; 
    var newTerms = model.constraintTerms[model.constraintPosition];
    var clauseIndex = 0;
    
    if (model.constraintPosition > prevConstraintPosition) {
        log("trying to satisfy next constraint "+curConstraint);
        // init term values for next constraint:
        for (var i=0; i<newTerms.length; i++) {
            log('initialising denotation of '+newTerms[i]+' to 0');
            model.denotations[newTerms[i]] = 0;
        }
    }
    else {
        if (model.constraintPosition < prevConstraintPosition // backtracking
            && model.clauseIndex[model.constraintPosition] < curConstraint.length-1) {
            log("trying to satisfy a different member of "+curConstraint);
            clauseIndex = model.clauseIndex[model.constraintPosition]+1;
        }
        else {
            log("trying to satisfy "+curConstraint+" with different denotations");
            if (!model.iterateDenotations(newTerms)) {
                log("no more term denotations to try; backtracking.");
                if (model.constraintPosition == 0) {
                    log('nothing to backtrack to; increasing domain');
                    this.initNextModel();
                    return false;
                }
                model.constraintPosition--;
                // When we backtrack from a given constraint (say, Fb) to the
                // previous constraint (say, Fa) because Fb couldn't be satisfied,
                // we need to undo the partial interpretation of F that satisfied
                // Fa; but we don't want to anul the interpretation of the new terms
                // in the previous constraint: we want to check if the constraint
                // can be satisfied on the next iteration of the new terms. If we
                // succeed and we move forward again, we want to start from scratch
                // interpreting the new terms in the later constraint (Fb). So when
                // we backtrack from constraint Y to constraint X, we need to (1)
                // erase the interpretation of new terms in Y, and (2) erase the
                // partial interpretation of predicates that brought us from X to
                // Y. (1) is easy, but (2) isn't because constraints can have many
                // disjuncts and it's not trivial to figure out which disjunct
                // brought us forward; moreover, if we've set |F|(1)=true because we
                // have |a|=1 and wanted to satisfy Fa, we can only erase
                // |F|(1)=true if it wasn't already set by an earlier constraint
                // (say, Fc, under |c|=1). So we keep track of when a record in a
                // predicate extension is created. That is, this.extensions is an
                // array; this.extensions[0] contains the predicate interpretations
                // added for constraint 0, and so on.
                delete model.extensions[model.constraintPosition];
                for (var i=0; i<newTerms.length; i++) {
                    delete model.denotations[newTerms[i]];
                }
                return false;
            }
        }
    }
    
    // Let's see if we can extend the interpretation of predicates to satisfy
    // the constraint.
    if (this.model.satisfy(curConstraint, clauseIndex)) {
        log('constraint can be satisfied: '+this.model);
        // moving on to next constraint on next call:
        model.constraintPosition++;
        if (model.constraintPosition == model.constraints.length) {
            log("no more constraints to satisfy; we've found a model!");
            return true;
        }
        return false;
    }
    else {
        log("can't satisfy constraint"); // try with different denotations next time
        return false;
    }
} 

ModelFinder.prototype.initNextModel = function() {
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

function Model(modelfinder, numIndividuals, numWorlds) {
    // initialize model with fixed domain(s)

    this.modelfinder = modelfinder;
    this.parser = modelfinder.parser;

    // initialize domains:
    this.domain = [];
    for (var i=0; i<numIndividuals; i++) {
        this.domain.push(i); // domain is integers 0,1,...
    }
    this.worlds = [];
    for (var i=0; i<numWorlds; i++) {
        this.worlds.push(i); // world domain is also integers 0,1,...
    }
    this.isModal = numWorlds > 0;
    log('Model domain '+this.domain+', worlds '+this.worlds);

    // initialize interpretation:
    this.denotations = {}; // term extensions, e.g. 'a' => 0, '[f,a]' => 2
    this.extensions = []; // predicate extensions, e.g. [0] => ['G','a',true]
    this.clauseIndex = []; // stores which disjunct in each clause we're currently satisfying; e.g. [0] => 2
    
    // replace universal variables in modelfinder.clauses by domain elements:
    this.constraints = this.getConstraints();

    // see modelfinder.nextStep() for the purpose of the following attributes
    this.constraintTerms = this.getConstraintTerms();
    this.constraintPosition = 0;
    this.prevConstraintPosition = -1;
    
}

Model.prototype.getConstraints = function() {
    // turn modelfinder.clauses into a variable-free list of clauses that serves as
    // constraints on interpretations. Each list in this.constraints is
    // interpreted as a disjunction of its members. If the domain is [0,1], then
    // a clause ['Fx','xRy'] is turned into ['F0','0R0'], ['F0','0R1'],
    // ['F1','1R0'], ['F1','1R1'].
    res = [];
    log('making constraints');
    for (var c=0; c<this.modelfinder.clauses.length; c++) {
        var clause = this.modelfinder.clauses[c];
        log('  clause '+clause);
        // collect all variables in the clause:
        var variables = [];
        for (var i=0; i<clause.length; i++) {
            variables = variables.concatNoDuplicates(this.parser.getVariables(clause[i]));
        }
        if (variables.length == 0) {
            // log('    adding clause to constraint');
            res.push(clause);
            continue;
        }
        // get all possible interpretations of the variables:
        var interpretations = this.getVariableAssignments(variables);
        log('    variables: '+variables+', interpretations: '+interpretations);
        // e.g. [[0,0],[0,1],[1,0],[1,1]] for two variables and domain [0,1]
        for (var i=0; i<interpretations.length; i++) {
            var interpretation = interpretations[i];
            log('    adding clause for interpretation '+interpretation);
            var nclause = clause.map(function(formula) {
                var nformula = formula;
                for (var i=0; i<variables.length; i++) {
                    nformula = nformula.substitute(variables[i], interpretation[i]);
                }
                log(nformula.string);
                return nformula;
            });
            res.push(nclause);
        }
    }
    log('constraints: '+res);
    res = this.modelfinder.simplifyClauses(res);
    log('simplified constraints: '+res);
    return res;
}

Model.prototype.getVariableAssignments = function(variables) {
    // list all interpretations of <variables> on the model's domain(s), as
    // sequences; e.g. [[0,0],[0,1],[1,0],[1,1]] for domain=[0,1] and two
    // individual variables.
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
    // changes tuple to the next tuple in the list of all tuples of the same
    // length whose i-the element is one of {0..maxValues[i]}
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

Model.prototype.getConstraintTerms = function() {
    // returns list of new terms for each constraint (as strings); i.e.,
    // position 2 in the list is a list of terms that first occur in the second
    // constraint. Terms include subterms; see this.denotationsAreConsistent()
    // for why. As a side-effect, we define modelfinder.isWorldTerm as a dict
    // that's true for terms denoting worlds. (Must be done here because a world
    // term might look like this: 'f(3)'.)
    var res = [];
    var termIsOld = {};
    for (var i=0; i<this.constraints.length; i++) {
        var clause = this.constraints[i];
        var constraintTerms = [];
        for (var j=0; j<clause.length; j++) {
            var atom = clause[j].sub || clause[j];
            var terms = atom.terms.copy();
            if (this.parser.isModal) {
                if (atom.predicate == this.parser.R) {
                    this.modelfinder.isWorldTerm[terms[0].toString()] = true;
                    this.modelfinder.isWorldTerm[terms[1].toString()] = true;
                }
                else {
                    var lastTerm = terms[terms.length-1].toString();
                    this.modelfinder.isWorldTerm[lastTerm] = true;
                }
            }
            for (var k=0; k<terms.length; k++) {
                if (typeof terms[k] == 'number') continue;
                // terms[k] is something like 'a' or ['f', 'b']
                var term = terms[k].toString();
                if (termIsOld[term]) continue;
                termIsOld[term] = true;
                constraintTerms.push(term);
                if (terms[k].isArray) {
                    for (var l=1; l<terms[k].length; l++) {
                        terms.push(terms[k][l]);
                        if (this.modelfinder.isWorldTerm[term]) {
                            // subterms of world terms are world terms
                            this.modelfinder.isWorldTerm[terms[k][l].toString()] = true;
                        }
                    }
                }
            }
        }
        res.push(constraintTerms);
    }
    return res;
}

Model.prototype.iterateDenotations = function(terms) {
    // return next possible assignment of denotations to <terms>. We want to
    // avoid redundant permutations here. For example, there's no point trying
    // |a|=0, |b|=1 and later |a|=1, |b|=0. So we fix the first constant to
    // always denote 0. The second either denotes 0 or (if available) 1, but
    // never 2. And so on. xxx can we also do this for functional terms? Not
    // obvious how: f(0) isn't even in the list of all terms.

    for (var i=terms.length-1; i>=0; i--) {
        var term = terms[i];
        var maxValue = this.modelfinder.isWorldTerm[term] ?
            this.worlds.length-1 : this.domain.length-1;
        if (term[0] != '[') { // name
            var termIndex = this.modelfinder.names.indexOf(term);
            if (termIndex == -1) {
                termIndex = this.modelfinder.worldNames.indexOf(term);
            }
            if (termIndex != -1) {
                maxValue = Math.min(maxValue, termIndex);
            }
        }
        if (this.denotations[term] < maxValue) {
            this.denotations[term]++;
            log("increasing denotation of "+term+" to "+this.denotations[term]);
            return true;
        }
        else {
            log(term+" has max denotation "+maxValue+"; setting to 0");
            this.denotations[term] = 0;
            // now try to increment denotation of previous term 
        }
    }
    return false;
}


Model.prototype.satisfy = function(clause, startIndex) {
    // tries to extend this.extensions for the predicates so as to satisfy the
    // clause, ignoring disjuncts before <startIndex>. Before we do that, we
    // take care of another issue. When looking for models, we treat all terms
    // as black boxes, assigning them denotations with no regard to the
    // denotations assigned to other terms. This is much faster than iterating
    // through all possible denotations for all function symbols, but it allows
    // for inconsistent denotation assignments where e.g. |f(a)|=0, |f(0)|=1,
    // and |f(f(a))|=0. Since the present function is called whenever
    // this.denotations has been modified, we use it to test whether the
    // denotations are consistent. If not, we return false, which will trigger a
    // change in this.denotations and another call of this function, etc. xxx
    // TODO denotationsAreconsistent should be made redundant by making
    // iterateDenotations smarter: skip inconsistent term assignments
    if (!this.denotationsAreConsistent()) return false;
    // xxx first check if clause is already satisfied?
    startIndex = startIndex || 0;
    for (var i=startIndex; i<clause.length; i++) {
        log("trying to satisfy "+clause[i].string);
        var atom = clause[i].sub || clause[i];
        var tv = clause[i].sub ? false : true;
        var predicate = atom.predicate;
        var args = [];
        for (var j=0; j<atom.terms.length; j++) {
            var term = atom.terms[j];
            if (typeof term == 'number') args.push(term);
            else args.push(this.denotations[term.toString()]);
        }
        var argsStr = args.toString();
        var storedTv = this.evaluatePredication(predicate, argsStr);
        if (storedTv !== null) {
            if (storedTv == tv) {
                log("   "+predicate+" applied to "+argsStr+" already equals "+tv);
                // no point trying other disjuncts when backtracking:
                this.clauseIndex[this.constraintPosition] = clause.length-1;
                return true;
            }
            log("   failed: "+predicate+" applied to "+argsStr+" equals "+storedTv);
            continue;
        }
        log("  setting extension of "+predicate+" for "+argsStr+" to "+tv);
        this.extensions[this.constraintPosition] = [predicate, argsStr, tv];
        this.clauseIndex[this.constraintPosition] = i;
        return true;
    }
    return false;
}

Model.prototype.evaluatePredication = function(predicate, argsStr) {
    // returns the truth-value of the predicate applied to argsStr, on the
    // present interpretation, or null if the predicate is undefined for
    // argsStr.

    // Recall that this.extensions is a (gappy) list that stores for each
    // constraintPosition at which a predicate was partially interpreted a
    // triple of the predicate, the argsStr and the truth-value.
    for (var i=0; i<this.extensions.length; i++) {
        if (this.extensions[i] &&
            this.extensions[i][0] == predicate &&
            this.extensions[i][1] == argsStr) {
            return this.extensions[i][2];
        }
    }
    return null;
}

Model.prototype.denotationsAreConsistent = function() {
    // tests if the assignment of denotations to singular terms is inconsistent,
    // like |a|=0, |f(0)|=1 and |f(a)|=0, or |f(a)|=0, |f(0)|=1, and
    // |f(f(a))|=0.

    // We go through all terms for which we know an denotation. For example,
    // suppose we know that |f(a)|=0. Whenever f(a) then occurs in another term
    // of which we know the denotation, we can replace it by 0 and register the
    // denotation of the resulting term. E.g. if we have |f(f(a))|=1, we register
    // the new fact |f(0)|=1. Whenever we "register" a fact, we check if it
    // contradicts what we already know.
    //
    // In the example |a|=0, |f(0)|=1, and |f(a)|=0, processing |a|=0 leads to
    // registering the fact |f(0)|=0, from |f(a)|=1; we get a contradiction.
    //
    // In the other example, substituting |f(a)|=0 in |f(f(a))|=0 leads to
    // |f(0)|=0, contradicting |f(0)|=1.
    //
    // A trickier case: |a|=0, |f(a)|=0, |f(f(0))|=1. We first register
    // |f(0)|=0. That's not yet a contradiction. We also need to process what we
    // now found out about f(0), substituting it in f(f(0)). So when we loop
    // through all terms for which we know an denotation, we have to loop not
    // just through this.denotations.
    //
    // What if we have |f(a)|=0, and |f(f(a))|=1? We get |f(0)|=1. This entails
    // that |a| is not 0. Now what if we also have |f(b)|=1 and |b|=1? We get
    // |f(1)|=1, in addition to |f(0)|=1. If 0 and 1 are the only domain
    // elements, this contradicts |f(a)|=0. Argh.
    //
    // Maybe we need to interpret not only occurrent terms but also subterms. So
    // if we have f(f(a)) in a formula, we need to assign denotations to a, f(a),
    // and f(f(a)). (But we don't need to interpret f for all possible
    // arguments.) Should this interpretation of subterms happen here or as part
    // of the main term assignment? If it happens there, we'll iterate through
    // all possible assignments to a, f(a), and f(f(a)) even though only f(f(a))
    // occurs in the formula we want to satisfy, so it seems pointless to vary
    // f(a) without varying f(f(a)). -- Well, except that this might make the
    // assignment consistent.

    // xxx TODO check (i.e. prove) that this covers all cases

    var denotations = {}; // Here we register new facts about denotations
    var interpretedExpressions = Object.keys(this.denotations); // this will grow
    for (var i=0; i<interpretedExpressions.length; i++) {
        var expr = interpretedExpressions[i]; // e.g. '[f,[f,a]]' or 'a'
        denotations[expr] = this.denotations[expr];
    }
    for (var i=0; i<interpretedExpressions.length; i++) {
        var expr = interpretedExpressions[i];
        for (var j=0; j<interpretedExpressions.length; j++) {
            var expr2 = interpretedExpressions[j];
            if (expr2.indexOf(expr) > 0) {
                var newExpr2 = expr2.replace(expr, denotations[expr]);
                log(expr2+" contains "+expr+"; equivalent to "+newExpr2);
                if (!(newExpr2 in denotations)) {
                    denotations[newExpr2] = denotations[expr2];
                    interpretedExpressions.push(newExpr2);
                }
                else if (denotations[newExpr2] != denotations[expr2]) {
                    log(expr2+" denotes "+denotations[expr2]+"; but "+newExpr2+" "+denotations[newExpr2]);
                    log("term denotations are inconsistent");
                    return false; 
                }
            }
        }
    }
    return true;
}

Model.prototype.extendToSatisfy = function(formula) {
    // This function is not used in the modelfinder, but to read
    // off countermodels from open trees, in sentree.js. Here the
    // domain has been fixed by the terms on the tree and we need
    // to find a suitable interpretation of the predicates. The
    // matter is not entirely trivial because this.extensions is
    // indexed by constraintPositions. Hence this wrapper function
    // to satisfy().
    if (!this.satisfy([formula])) return false;
    this.constraintPosition++;
    return true;
}

Model.prototype.toHTML = function() {
    var str = "<table>";
    if (this.parser.isModal) {
        str += "<tr><td>Worlds: </td><td align='left'>{ ";
        str += this.worlds.join(", ");
        str += " }</td></tr>\n";
        if (!this.parser.isPropositional) {
            str += "<tr><td>Individuals: </td><td align='left'>{ ";
            str += this.domain.join(", ");
            str += " }</td></tr>\n";
        }
    }
    else if (!this.parser.isPropositional) {
        str += "<tr><td>Domain: </td><td align='left'>{ ";
        str += this.domain.join(", ");
        str += " }</td></tr>\n";
    }

    // display constants and function symbols:
    // a: 0
    // f: { <0,1>, <1,1> }
    
    var termExtensions = this.getTermExtensions();

    for (var i=0; i<this.modelfinder.constants.length; i++) {
        var sym = this.modelfinder.constants[i];
        var ext = termExtensions[sym];
        var val = ext;
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    
    for (var i=0; i<this.modelfinder.funcSymbols.length; i++) {
        var sym = this.modelfinder.funcSymbols[i];
        var ext = termExtensions[sym];
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

    var predicateExtensions = this.getPredicateExtensions();
    
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        var sym = this.modelfinder.predicates[i];
        var ext = predicateExtensions[sym];
        var val;
        if (!ext.isArray) { // zero-ary
            val = ext;
        }
        else if (ext.length > 0 && !ext[0].isArray) {
            // ext is something like [1,2]
            val = '{ '+ext.join(',')+' }';
        }
        else {
            // ext is something like [[0,1],[1,1]]
            val = '{ '+ext.map(function(tuple) {
                return '('+tuple.join(',')+')';
            }).join(', ')+' }';
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    
    str += "</table>";
    return str;
}

Model.prototype.getTermExtensions = function() {
    // this.denotations is a dict with entries like '[f,a]' => 0, 'a' => 1.  We
    // return a new dict that assigns extensions to all function symbols and
    // constants in initFormulas, with records like 'f' => [(1,0),(0,1)].
    var result = {};
    var denotations = this.denotations; // 'this' not available in replace function below 
    var interpretedTerms = Object.keys(denotations);
    for (var i=0; i<this.modelfinder.constants.length; i++) {
        var cons = this.modelfinder.constants[i];
        result[cons] = denotations[cons] || 0;
    }
    for (var i=0; i<this.modelfinder.funcSymbols.length; i++) {
        var fs = this.modelfinder.funcSymbols[i];
        // If fs is 'f', we have records in denotations for things like
        // '[f,0]' or '[f,a]' or '[f,[f,a]]'. We will then also have
        // records for the subterms.
        result[fs] = [];
        // log("constructing extension for "+fs+" (arity "+this.parser.arities[fs]+")");
        for (var j=0; j<interpretedTerms.length; j++) {
            var expr = interpretedTerms[j];
            if (expr.indexOf('['+fs+',') == 0) { // '[f,a]' or '[f,[f,a]]', etc.
                // log("   we know that "+expr+" = "+denotations[expr]);
                // replace complex arguments like '[f,a]' by their denotation: 
                var expr2 = expr.slice(1,-1).replace(/\[.+?\]/, function(m) {
                    return denotations[m] || '0';
                });
                // log("   subterms replaced: "+expr2);
                var args = expr2.split(',');
                args.shift(); 
                // convert simple arguments like 'a' to numbers:
                for (var k=0; k<args.length; k++) {
                    if (isNaN(args[k])) { // isNaN('1') == false 
                        args[k] = denotations[args[k]] || 0;
                    }
                }
                var value = denotations[expr];
                // log("   adding "+args+" => "+value);
                result[fs].push(args.concat([value]));
            }
        }
        log("  "+result[fs]);
        // xxx make sure functions are total?
    }
    return result;
}

Model.prototype.getPredicateExtensions = function() {
    // this.extensions is a list with entries like ['p','[]',true] and
    // ['F','[0,0]',false]. We return a dict that assigns extensions to all
    // predicates in initFormulas, with records like 'F' => [[0,1],[1,0]].
    var result = {};
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        // Zero-ary predicates will have truth-values as extensions, one-ary
        // predicates list of individuals, other predicates lists of lists of
        // individuals.
        var pred = this.modelfinder.predicates[i];
        result[pred] = (this.parser.arities[pred] == 0) ? false : [];
        // NB: modal proposition letters have arity 1 
        for (var j=0; j<this.extensions.length; j++) {
            if (!this.extensions[j] || this.extensions[j][0] != pred) continue;
            var argsStr = this.extensions[j][1]; // e.g. '[0]' or '[0,2]'
            var tv = this.extensions[j][2];
            if (argsStr == '[]') { // proposition letter
                result[pred] = tv;
                break;
            }
            if (!tv) continue; // only list positive extension
            var args = argsStr.slice(1,-1).split(',');
            if (args.length == 1) {
                result[pred].push(args[0]);
            }
            else {
                result[pred].push(args);
            }
        }
    }
    return result;
}

Model.prototype.toString = function() {
    // for debugging
    return this.toHTML().replace(/<.+?>/g, '');
}
