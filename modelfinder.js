// Often there are simple countermodels that are hard to find through the tree
// method; so we run a separate algorithm to find such countermodels.
//
// This works as follows.
//
// 1. We transform initFormulas into clausal normal form, giving us literal
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
//    replaced by two constraints, F0 and F1. [Note that numerals are not
//    allowed as terms, so there can be no clash. xxx check]
//
// 4. Now we go through all the constraints (which are lists of literals,
//    interpreted disjunctively). If a constraint contains uninterpreted terms,
//    we also go through all ways of assigning to them members of the domain as
//    referents. (We don't assign a meaning to function symbols here, only to
//    complete terms like f(a,g(b)).)  For each of these assignments, we try to
//    satisfy the constraint by extending the interpretation of the
//    predicates. (For example, if we need to satisfy F0, we check if |F| is
//    already defined for 0; if not, we set |F|(0)=true; if |F| is defined and
//    |F|(0)=true, we continue; if |F|(0)=false, we give up.) Whenever the
//    constraint is satisfied, we move on to the next constraint. If
//    satisfaction is impossible, we backtrack and try another interpretation of
//    the individuals.
//
// Modal models have two domains, W and D. When breaking down initFormulas into
// constraints, we take into account which variables quantify over worlds and
// which over individuals. Accessibility conditions like reflexivity are added
// to the constraints.
//
//
// Some more details on how we store models/interpretations:
//
// A first-order model has a domain D and an interpretation function assigning
//
// - to each 0-ary individual functor a member of D,
// - to each n-ary individual functor a function from n-tuples to members of D,
// - to each 0-ary predicate a truth-value,
// - to each n-ary predicate a function from n-tuples to truth-values.
//
// We store the interpretation function in model.values. However, JS doesn't
// allow lists as dict keys. So values['P'] can't be a dict mapping, say,
// <0,2> to true.
//
// We get around this by replacing the dict values with simple lists: instead of
// 'P' -> { [0,0]: true, [0,1]: false, ... }, we have 'P' -> [true, false,
// ... ]; the nth value in the list is the value assigned to the nth 2-tuple
// from the domain. So to find out whether [0,1] in |P|, we have to determine
// the position of [0,1] in the list of all 2-tuples from the domain, and then
// look up that position in values['P'].
//
// Instead of computing the relevant number list position on the fly, we use a
// lookup table in which tuples are converted to strings. For example, we have
// model.argLists['P'] = ['[0,0]', '[0,1]', '[1,0]', '[1,1]'].  So to find the
// value assigned to 'P' for [0,1], we first look up the index of '[0,1]' in
// argLists['P'], and then return that index from values['P']. This format is
// convenient because to iterate over possible interpretations 'P', we simply
// need to turn an array like [0,0,0,1] (representing truth-values) into
// [0,0,1,0]. (Different binary predicates will share the same argList.)
//
// For zero-ary predicates and zero-ary functors (constants), there is only one
// possible argument list: the empty list. It's more efficient to store
// values[a] = 0, values[p] = true directly, bypassing argLists.
//
// Modal models have a further domain W. The elements of W are also natural
// numbers starting with 0. That's OK: nothing in the definition of a Kripke
// model requires that the worlds must be distinct from the individuals; note
// that we can still have more worlds than individuals or more individuals than
// worlds.
//
// In modal models, all predicates take a world as their last argument; 'R'
// takes two worlds, function terms only take individuals. That's why we have to
// associate argLists with symbols rather than store them by arity, as
// argLists[1], argLists[2], etc. For example, argLists['R'] is the list of all
// pairs taken from W, while argLists['f'] for binary 'f' may be the list of all
// pairs taken from D.

function ModelFinder(initFormulas, accessibilityConstraints) {
    log("creating ModelFinder");

    // break down initFormulas and accessibilityConstraints into clauses:
    initFormulas = initFormulas.concat(accessibilityConstraints || []);
    this.clauses = this.getClauses(initFormulas);
    
    // collect symbols that need to be interpreted (including skolem symbols):
    this.parser = initFormulas[0].parser;
    this.predicates = [];
    this.constants = [];
    this.terms = [];
    for (var i=0; i<this.clauses.length; i++) {
        for (var j=0; j<this.clauses[i].length; j++) {
            var atom = this.clauses[i][j].sub || this.clauses[i][j];
            this.terms = this.terms.concatNoDuplicates(atom.terms);
            this.constants = this.constants.concatNoDuplicates(atom.constants);
            this.predicates = this.predicates.concatNoDuplicates(atom.predicates);
        }
    }
    
    // but also store original list of constants without skolem symbols to
    // display in the printed model:
    this.origConstants = [];
    for (var i=0; i<initFormulas.length; i++) {
        this.origConstants = this.origConstants.concatNoDuplicates(initFormulas[i].constants);
    }

    // initialize model:
    var numIndividuals = 1;
    var numWorlds = this.parser.isModal ? 1 : 0;
    this.model = new Model(this, numIndividuals, numWorlds);
}

ModelFinder.prototype.getClauses = function(formulas) {
    // converts the formulas in <formulas> into clausal normal form and returns
    // combined list of clauses
    var res = [];
    formulas.forEach(function(formula) {
        log('getting clauses from '+formula);
        var clauses = formula.clausalNormalForm();
        res = res.concatNoDuplicates(clauses);
    });
    log('all clauses: '+res);
    // xxx TODO: simplify clauses! xxx that function should also be called
    // within clausalnormalform to return a simpler list.
    
    // order clauses by simplicity (number of disjuncts):
    res.sort(function(a,b){ return a.length > b.length; });
    return res;
}

ModelFinder.prototype.nextStep = function() {
    // Each call of this function tries to satisfy one constraint, namely
    // model.constraints[model.constraintPosition]. We need to do slightly
    // different things depending on whether we're processing this constraint
    // for the first time or not. If it's the first time, we (1) assign all new
    // terms the extension 0; then we (2) see if there's an interpretation of
    // the predicates that satisfies the constraint; if yes, we move on to the
    // next constraint on the next call; if no, we process the same constraint
    // again. If we process the same constraint again, we (1') try to find a new
    // assignment of extensions to the new terms; if there's none, we backtrack
    // to earlier constraints (which will be processed again at that point) or
    // increase the domain if there are no earlier constraints; if there is a
    // new assignment of terms, we go through (2) as above.

    var model = this.model;
    var curConstraint = model.constraints[model.constraintPosition];
    var newTerms = model.constraintTerms[model.constraintPosition];

    if (model.constraintPosition > model.prevConstraintPosition) {
        log("trying to satisfy next constraint "+curConstraint);
        // init term values for next constraint:
        for (var i=0; i<newTerms.length; i++) {
            log('initialising extension of '+newTerms[i]+' to 0');
            model.extensions[newTerms[i]] = 0;
        }
        model.prevConstraintPosition = model.constraintPosition;
    }
    else {
        model.prevConstraintPosition = model.constraintPosition;
        log("trying to satisfy constraint "+curConstraint+" with different term extension");
        if (!model.iterateTermExtensions(newTerms)) {
            log("no more term extensions to try; backtracking.");
            if (model.constraintPosition == 0) {
                log('nothing to backtrack to; increasing domain');
                this.initNextModel();
                return false;
            }
            model.constraintPosition--;
            // When we backtrack to an earlier constraint, we want to erase the
            // (partial) interpretations of predicates and terms made for later
            // constraints. IterateTermExtensions conventiently leaves all new
            // terms in their initial interpretation, denoting 0. But we also
            // want to undo partial predicate interpretations made to satisfy
            // the previous constraint before we go back to it. E.g. if we've
            // set |F|(0,1)=true because we had |a|=0, |b|=1 and the previous
            // constraint was Fab, we want to erase this value of |F| before
            // setting |a|=0, |b|=2. But how do we know what to erase?
            // |F|(0,1)=true may have been forced already by an earlier
            // constraint. So we store earlier interpretations of the
            // predicates. That is, when turning to a constraint "from below",
            // we store the present extension of all predicates. If we revert to
            // that constraint "from above", we first set the extension back to
            // that record.
            model.extensions = model.storedExtensions[model.constraintPosition];
            return false;
        }
    }
        
    // Let's see if we can extend the interpretation of predicates to satisfy
    // the constraint.
    if (this.model.satisfy(curConstraint)) {
        log('constraint can be satisfied: '+this.model);
        // moving on to next constraint on next call:
        model.constraintPosition++;
        if (model.constraintPosition == model.constraints.length) {
            log("no more constraints to satisfy; we've found a model!");
            return true;
        }
        // store current extensions for backtracking:
        if (model.constraintPosition > 0) {
            model.storedExtensions[model.constraintPosition-1] = model.copyExtensions(); // xxx only need to preserve predicate extensions
        }
        return false;
    }
    else {
        log("can't satisfy constraint"); // try with different extensions next time
        return false;
    }
} 

ModelFinder.prototype.initNextModel = function() {
    var numWorlds = this.model.worlds.length;
    var numIndividuals = this.model.domain.length;
    if (numWorlds && numWorlds < this.model.domain.length) {
        numWorlds++;
    }
    else {
        numIndividuals++; // xxx this means we're looking at QML models even for PML!
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
    for (var i=0; i<modelfinder.numWorlds; i++) {
        this.worlds.push(i); // world domain is also integers 0,1,...
    }
    this.isModal = numWorlds > 0;

    // initialize interpretation function:
    
    this.argLists = {}; // will store all possible arguments for all symbols, as
                        // strings, e.g. 'P' => ['[0,0],[0,1],...'].
    
    this.values = {}; // symbol => extension for zero-ary expressions, otherwise
                      // symbol => list of extensions corresponding to the list
                      // of arguments in this.argLists[symbol].

    this.extensions = {}; // 'P' => { '[0,1]' => true, '[1,1]' => false }
                          // 'f(a)' => 0
    
    // replace universal variables in modelfinder.clauses by domain elements:
    this.constraints = this.getConstraints();
    // See modelfinder.nextStep() for the purpose of the following attributes.
    this.constraintTerms = this.getConstraintTerms();
    this.constraintPosition = 0;
    this.prevConstraintPosition = -1;
    this.storedExtensions = []; 
    
    // The following dictionaries will come in handy:
    // modelfinder.predicates.map(function(x){ this[x]=true; }, this.isPredicate={});
    // modelfinder.constants.map(function(x){ this[x]=true; }, this.isConstant={});
    // this.maxValue = [];
    // for (var i=0; i<modelfinder.predicates.length; i++) {
    //     this.maxValue[modelfinder.predicates[i]] = 1; // true
    // }
    // for (var i=0; i<modelfinder.constants.length; i++) {
    //     this.maxValue[modelfinder.constants[i]] = this.domain.length-1;
    // }
    // if (this.isModal) {
    //     // The only world-denoting constant in initFormulas is 'w'; variables
    //     // have been replaced by numbers already (see getConstraints).
    //     this.maxValue[this.parser.w] = this.worlds.length-1;
    // }
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
        clause.forEach(function(formula) {
            variables = variables.concatNoDuplicates(formula.variables);
        });
        if (variables.length == 0) {
            // log('    adding clause to constraint');
            res.push(clause);
            continue;
        }
        // get all possible interpretations of the variables:
        var interpretations = Model.listTuples(this.domain, variables.length); // xxx treat modal variables specially!
        log('    variable interpretations: '+interpretations);
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
    return res;
}

Model.listTuples = function(domain, arity) {
    // xxx cache!
    var res = [];
    var maxValue = domain.length-1;
    var tuple = Array.getArrayOfZeroes(arity);
    res.push(tuple.copy());
    while (Model.iterateTuple(tuple, maxValue)) { // optimise?
        res.push(tuple.copy());
    }
    // log(res.toString());
    return res;
}

Model.crossProduct = function(tuples, set) {
    var res = [];
    for (var i=0; i<tuples.length; i++) {
        for (var j=0; j<set.length; j++) {
            res.push(tuples[i].concat([set[j]]));
        }
    }
    return res;
}

Model.iterateTuple = function(tuple, maxValue) { // xxx should be array property?
    // changes tuple to the next tuple in the list of the cartesian powers of
    // {0..maxValue}, with power <tuple>.length.
    for (var i=tuple.length-1; i>=0; i--) {
        if (tuple[i] < maxValue) {
            tuple[i]++;
            return true;
        }
        tuple[i] = 0;
    }
    return false;
    // Example 1: tuple = 011, maxValue = 2.
    //   at i=2, tuple -> 012, return true
    // Example 2: tuple = 011, maxValue = 1.
    //   at i=2, tuple -> 010
    //   at i=1, tuple -> 000
    //   at i=0, tuple -> 100, return true
}

Model.prototype.getConstraintTerms = function() {
    // returns list of new terms for each constraint; i.e., position 2 in the
    // list is a list of terms that first occur in the second constraint. Terms
    // include subterms; see this.extensionsAreconsistent() for why.
    var res = [];
    var termIsOld = {};
    for (var i=0; i<this.constraints.length; i++) {
        var clause = this.constraints[i];
        var constraintTerms = [];
        for (var j=0; j<clause.length; j++) {
            var atom = clause[j].sub || clause[j];
            var terms = atom.terms.copy();
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
                    }
                }
            }
        }
        res.push(constraintTerms);
    }
    return res;
}

Model.prototype.initNextConstraintInterpretation = function() {
}

Model.prototype.copyExtensions = function() {
    // returns a copy of extensions dictionary
    var result = [];
    for (p in this.extensions) {
        if (this.extensions.hasOwnProperty(p)) {
            result[p] = this.extensions[p];
        }
    }
    return result;
}



Model.prototype.iterateTermExtensions = function(terms) {
    // return next possible assignment of extensions to <terms>. We want to
    // avoid redundant permutations here. For example, there's no point trying
    // |a|=0, |b|=1 and later |a|=1, |b|=0. So we fix the first term to always
    // denote 0. The second term either denotes 0 or (if available) 1, but never
    // 2. The third term denotes 0 or 1 or 2, etc.

    for (var i=terms.length-1; i>=0; i--) {
        var term = terms[i];
        var termIndex = this.modelfinder.terms.indexOf(term);
        var maxValue = Math.max(termIndex, this.domain.length-1); // xxx dist world terms from ind terms
        if (this.extensions[term] < maxValue) {
            this.extensions[term]++;
            log("setting extension of "+term+" to "+this.extensions[term]);
            return true;
        }
        else {
            this.extensions[term] = 0;
            log("setting/keeping extension of "+term+" at "+0);
            // now try to increment extension of previous term 
        }
    }
    return false;
}


// Model.prototype.getConstraintSymbols = function() {
//     var res = [];
//     var symbolIsOld = {};
//     for (var i=0; i<this.constraints.length; i++) {
//         var clause = this.constraints[i];
//         var symbols = [];
//         for (var j=0; j<clause.length; j++) {
//             var formulaSymbols = clause[j].predicates.concat(clause[j].constants);
//             for (var k=0; k<formulaSymbols.length; k++) {
//                 var sym = formulaSymbols[k];
//                 if (typeof sym != 'number' && !symbolIsOld[sym]) {
//                     symbols.push(sym);
//                     symbolIsOld[sym] = true;
//                 }
//             }
//         }
//         res.push(symbols);
//     }
//     return res;
// }


Model.prototype.satisfy = function(clause) {
    // tries to extend this.extensions for the predicates so as to satisfy the
    // clause. However, before we do that, we take care of another issue. When
    // looking for models, we treat all terms as black boxes, assigning them
    // extensions with no regard to the extensions assigned to other terms. This
    // is much faster than iterating through all possible extensions for all
    // function symbols, but it allows for inconsistent extension assignments
    // where e.g. |f(a)|=0, |f(0)|=1, and |f(f(a))|=0. Since the present
    // function is called whenever this.extensions has been modified, we use it
    // to test whether the extensions are consistent. If not, we return false,
    // which will trigger a change in this.extensions and another call of this
    // function, etc. TODO extensionsAreconsistent should be made redundant by
    // making iterateTermExtensions smarter: skip inconsistent term assignments
    if (!this.extensionsAreConsistent()) return false;
    for (var i=0; i<clause.length; i++) {
        log("trying to satisfy "+clause[i].string);
        var atom = clause[i].sub || clause[i];
        var tv = clause[i].sub ? false : true;
        var predicate = atom.predicate;
        var args = [];
        for (var j=0; j<atom.terms.length; j++) {
            var term = atom.terms[j];
            if (typeof term == 'number') args.push(term);
            else args.push(this.extensions[term.toString()]);
        }
        var argsStr = args.toString();
        if (!this.extensions[predicate]) {
            this.extensions[predicate] = {};
            this.extensions[predicate][argsStr] = tv;
            log("  initialising predicate extension for "+argsStr+" to "+tv);
            return true;
        }
        if (!(argsStr in this.extensions[predicate])) {
            this.extensions[predicate][argsStr] = tv;
            log("  setting predicate extension for "+argsStr+" to "+tv);
            return true;
        }
        if (this.extensions[predicate][argsStr] == tv) {
            log("  predicate extension for "+argsStr+" already equals "+tv);
            return true;
        }
        log("  failed");
    }
    return false;
}

Model.prototype.extensionsAreConsistent = function() {
    // tests if the assignment of extensions to singular terms is inconsistent,
    // like |a|=0, |f(0)|=1 and |f(a)|=0, or |f(a)|=0, |f(0)|=1, and
    // |f(f(a))|=0.

    // We go through all terms for which we know an extension. For example,
    // suppose we know that |f(a)|=0. Whenever f(a) then occurs in another term
    // of which we know the extension, we can replace it by 0 and register the
    // extension of the resulting term. E.g. if we have |f(f(a))|=1, we register
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
    // through all terms for which we know an extension, we have to loop not
    // just through this.extensions.
    //
    // What if we have |f(a)|=0, and |f(f(a))|=1? We get |f(0)|=1. This entails
    // that |a| is not 0. Now what if we also have |f(b)|=1 and |b|=1? We get
    // |f(1)|=1, in addition to |f(0)|=1. If 0 and 1 are the only domain
    // elements, this contradicts |f(a)|=0. Argh.
    //
    // Maybe we need to interpret not only occurrent terms but also subterms. So
    // if we have f(f(a)) in a formula, we need to assign extensions to a, f(a),
    // and f(f(a)). (But we don't need to interpret f for all possible
    // arguments.) Should this interpretation of subterms happen here or as part
    // of the main term assignment? If it happens there, we'll iterate through
    // all possible assignments to a, f(a), and f(f(a)) even though only f(f(a))
    // occurs in the formula we want to satisfy, so it seems pointless to vary
    // f(a) without varying f(f(a)). -- Well, except that this might make the
    // assignment consistent.

    // xxx TODO check (i.e. prove) that this covers all cases


    
    var extensions = {}; // Here we register new facts about extensions
    var interpretedExpressions = Object.keys(this.extensions); // this will grow
    for (var i=0; i<interpretedExpressions.length; i++) {
        var expr = interpretedExpressions[i]; // e.g. '[f,[f,a]]' or 'a' or 'F' (no harm)
        extensions[expr] = this.extensions[expr];
    }
    for (var i=0; i<interpretedExpressions.length; i++) {
        var expr = interpretedExpressions[i];
        for (var j=0; j<interpretedExpressions.length; j++) {
            var expr2 = interpretedExpressions[j];
            if (expr2.indexOf(expr) > 0) {
                var newExpr2 = expr2.replace(expr, extensions[expr]);
                log(expr2+" contains "+expr+"; equivalent to "+newExpr2);
                if (!(newExpr2 in extensions)) {
                    extensions[newExpr2] = extensions[expr2];
                    interpretedExpressions.push(newExpr2);
                }
                else if (extensions[newExpr2] != extensions[expr2]) {
                    log(expr2+" denotes "+extensions[expr2]+"; but "+newExpr2+" "+extensions[newExpr2]);
                    log("term extensions are inconsistent");
                    return false; 
                }
            }
        }
    }
    return true;
}

// Model.prototype.interpret = function(predicate, args) {
//     // tries to find an interpretation of <predicate> so that is satisfies
//     // <args>
//     var val = this.getValue(atom.predicate, args);
//     if (val) {
//         // predicate is already defined for args:
//         log('value is of atom is already set as '+val);
//         return val == tv;
//     }
//     if (atom.terms.length == 0) { // propositional constant
//         this.values[atom.predicate] = tv;
//         return true;
//     }
//     if (!model.values[atom.predicate]) {
//         // predicate is so far uninterpreted
//         var arity = atom.terms.length; 
//         this.argLists[atom.predicate] = Model.initArguments(arity, this.domain.length);
//     }
//     // make sure the value assigned to predicate for terms is tv:
//     var argsIndex = this.argLists[atom.predicate].indexOf(args.toString());
//     this.values[atom.predicate][argsIndex] = tv;
//     return true;
// }

// Model.prototype.interpretClause = function(clauseWithNumeralTerms) {
//     // tries to change the model so that it satisfies the clause (i.e. one
//     // literal in it); returns true if successful, false if not.
//     for (var i=0; i<clauseWithNumeralTerms.length; i++) {
//         var literal = clauseWithNumeralTerms[i];
//         if (this.interpret(literal)) return true;
//     }
//     return false;
// }
    
// Model.prototype.nextInterpretation = function(symbols) {
//     // iterate through all interpretations of <symbols> on the current
//     // domain(s).
//     if (!(symbols[0] in this.values)) {
//         log('initializing interpretation of symbols '+symbols+' (all values 0)');
//         this.initInterpretation(symbols);
//         return true;
//     }
//     // We go through all symbols. If the value assigned to the first isn't
//     // maximal, we increase it and return. If it's maximal, we set it back to
//     // zero and try increasing the value of the next symbol. So for two symbols
//     // with possible values 0,1 and 0,1,2 the interpretation goes through 0,0 ->
//     // 1,0 -> 0,1 -> 1,1 -> 0,2 -> 1,2.
//     for (var i=0; i<symbols.length; i++) {
//         var sym = symbols[i];
//         // Let's see if we can find a new interpretation of this symbol.
//         var maxValue = this.maxValue[sym];
//         if (!this.values[sym].isArray) { // zero-ary
//             if (this.values[sym] < maxValue) {
//                 // Yes, there's a new interpretation of sym; let's use it.
//                 this.values[sym]++;
//                 log('setting value of '+sym+' to '+this.values[sym]);
//                 return true;
//             }
//             // No; we've tried all interpretations of sym; let's reset it to its
//             // initial value and change the interpretation of the next symbol.
//             else {
//                 log(sym+' has max value; setting it to 0');
//                 this.values[sym] = 0;
//             }
//         }
//         else {
//             // Do the same for symbols that aren't zero-ary:
//             var iterated = Model.iterateTuple(this.values[sym], maxValue);
//             if (iterated) {
//                 log('setting value of '+sym+' to '+this.values[sym]);
//                 return true;
//             }
//             else {
//                 // Now we should reset the interpretation of sym to zero and iterate
//                 // over interpretation of next symbol; turns out iterateTuple
//                 // already sets this.values[sym] to zero if no iteration was
//                 // possible. So nothing left to do.
//                 log(sym+' has max value; setting it to '+this.values[sym]);
//             }
//         }
//     }
//     // No iteration possible.
//     log('no more interpretation of '+symbols);
//     return false;
// }

// Model.prototype.initInterpretation = function(symbols) {
//     // create first interpretation of <symbols>
//     for (var i=0; i<symbols.length; i++) {
//         var sym = symbols[i];
//         var arity = this.parser.arities[symbols[i]];
//         if (arity == 0) {
//             this.values[sym] = 0; // false or 1st individual/world (conveniently
//             log('initial value of '+sym+' is 0');
//         }
//         else {
//             this.argLists[sym] = this.initArgList(sym, arity);
//             this.values[sym] = Array.getArrayOfZeroes(this.argLists[sym].length);
//             // this.values[sym] is the list of values corresponding to the
//             // argument tuples in argLists[sym]; recall that 0 == false.
//             log('argList of '+sym+' is '+this.argLists[sym]);
//             log('initial values of '+sym+' are '+this.values[sym]);
//         }
//     }
// }

// Model.prototype.initArgList = function(symbol, arity) {
//     // return list of all possible arguments to |<symbol>|, as strings.
//     //
//     // For non-modal models, this is always the list of n-tuples from
//     // this.domain, where n is <symbol>'s arity.
//     //
//     // In modal models, function terms don't take worlds as arguments, so here
//     // we also return the list of n-tuples from this.domain; for normal
//     // predicates we instead return the list of (n-1)-tuples from this.domain X
//     // this.worlds; for 'R', we return the list of pairs from this.worlds.
//     var res = [];
//     var tuples = [];
//     if (!this.isModal) {
//         log('listing all '+arity+'-tuples from '+this.domain);
//         tuples = Model.listTuples(this.domain, arity);
//     }
//     else {
//         if (symbol == this.parser.R) {
//             tuples = Model.listTuples(this.worlds, 2);
//         }
//         else if (this.isPredicate[symbol]) {
//             tuples = Model.crossProduct(
//                 Model.listTuples(this.domain, arity-1),
//                 this.worlds
//             );
//         }
//         else {
//             tuples = Model.listTuples(this.domain, arity);
//         }
//     }
//     return tuples.map(function(x) { return x.toString() });
// }

// Model.prototype.removeInterpretation = function(symbols) {
//     // remove interpretation of <symbols> from this model
//     for (var i=0; i<symbols.length; i++) {
//         var sym = symbols[i];
//         delete this.values[sym];
//         if (sym in this.argLists) delete this.argLists[sym];
//     }
// } 


// Model.prototype.getValue = function(symbol, args) {
//     if (!args || args.length == 0) { // zero-ary proposition letter or ind constant
//         return this.values[symbol];
//     }
//     var argsIndex = this.argLists[symbol].indexOf(args.toString()); // optimise?
//     return this.values[symbol][argsIndex];
// }

// Model.prototype.iterate = function() { // remove xxx
//     // change this model to the next possible model.
//     //
//     // We need to change one thing at a time. E.g., if we have F and f, we need
//     // to iterate through all possible values for f for all possible values
//     // for F.
//     for (var i=0; i<this.symbols.length; i++) {
//         var sym = this.symbols[i];
//         var maxValue = this.isPredicate[sym] ? 1 : this.domain.length-1;
//         if (!this.values[sym].isArray) { // zero-ary
//             if (this.values[sym] < maxValue) {
//                 this.values[sym]++;
//                 return true;
//             }
//             else this.values[sym] = 0;
//         }
//         var iterated = Model.iterateTuple(this.values[sym], maxValue);
//         if (iterated) return true;
//         // Now reset interpretation of sym to zero and iterate interpretation of
//         // next symbol; turns out iterateTuple already sets this.values[sym] to
//         // zero if no iteration was possible. So nothing left to do.
//     }
//     // no iteration possible
//     this.initInterpretation(this.domain.length+1);
//     log('extending domain of modelfinder to '+this.domain);
// }

// Model.prototype.satisfies = function(clause) {
//     // tests if this model satisfies the given list of literals, interpreted disjunctively
//     for (var i=0; i<clause.length; i++) {
//         var literal = clause[i];
//         log('testing if model satisfies '+literal.string);
//         var atom = literal.sub || literal;
//         var args = [];
//         for (var i=0; i<atom.terms.length; i++) {
//             if (typeof atom.terms[i] == 'number') args.push(atom.terms[i]);
//             else args.push(this.interpretTerm(atom.terms[i]));
//         }
//         log('args: '+args);
//         var val = this.getValue(atom.predicate, args);
//         log('value is of atom is '+val);
//         var success = literal.sub ? !val : val;
//         if (success) return true;
//     }
//     return false;
// }

// Model.prototype.interpretTerm = function(term) {
//     if (term.isArray) {
//         var funcsym = term[0];
//         var args = [];
//         for (var i=1; i<term.length; i++) {
//             if (typeof term[i] == 'number') args.push(term[i]);
//             else args.push(this.interpretTerm(term[i]));
//         }
//         return this.getValue(funcsym, args);
//     }
//     return this.getValue(term);
// }

// Model.prototype.satisfiesInitFormulas = function() {
//     var initFormulas = this.modelfinder.initFormulas;
//     for (var i=0; i<initFormulas.length; i++) {
//         if (!this.satisfies(initFormulas[i])) {
//             log("no, model doesn't satisfy "+initFormulas[i].string);
//             return false;
//         }
//     }
//     log("yep, model satisfies initFormulas");
//     return true;
// }

Model.prototype.toHTML = function() {
    var str = "<table>";
    if (this.parser.isModal) {
        this.classifyDomain();
        str += "<tr><td>Worlds: </td><td align='left'>{ ";
        str += this.domainWorlds.join(", ");
        str += " }</td></tr>\n";
        if (this.domainIndividuals.length > 0) {
            str += "<tr><td>Individuals: </td><td align='left'>{ ";
            str += this.domainIndividuals.join(", ");
            str += " }</td></tr>\n";
        }
    }
    else if (!this.parser.isPropositional) {
        str += "<tr><td>Domain: </td><td align='left'>{ ";
        str += this.domain.join(", ");
        str += " }</td></tr>\n";
    }

    var extensions = this.completeExtensions();

    // xxx DRI in what follows
    
    // display constants and function symbols:
    // a: 0
    // f: { <0,1>, <1,1> }
    for (var i=0; i<this.modelfinder.origConstants.length; i++) {
        var sym = this.modelfinder.origConstants[i];
        var val;
        if (!extensions[sym].isArray) { // zero-ary
            val = extensions[sym];
        }
        // extensions[sym] is something like [1,2] or [[0,1],[1,1]]
        else if (extensions[sym].length > 0 && !extensions[sym][0].isArray) {
            // extensions[sym] is something like [1,2]
            val = '{ '+extensions[sym].join(',')+' }';
        }
        else {
        // extensions[sym] is something like [[0,1],[1,1]]
            val = '{ '+extensions[sym].map(function(tuple) {
                return '('+tuple.join(',')+')';
            }).join(',')+' }';
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    
    // display predicates and proposition letters:
    // p: true/1
    // F: { 0,1 }
    // G: { <0,0>, <1,1> }
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        var sym = this.modelfinder.predicates[i];
        var val;
        if (!extensions[sym].isArray) { // zero-ary
            val = extensions[sym];
        }
        else if (extensions[sym].length > 0 && !extensions[sym][0].isArray) {
            // extensions[sym] is something like [1,2]
            val = '{ '+extensions[sym].join(',')+' }';
        }
        else {
            // extensions[sym] is something like [[0,1],[1,1]]
            val = '{ '+extensions[sym].map(function(tuple) {
                return '('+tuple.join(',')+')';
            }).join(',')+' }';
        }
        str += "<tr><td align='right' class='formula'>" + sym + ": </td><td align='left'>" + val + "</td></tr>\n";
    }
    
    str += "</table>";
    return str;
}

Model.prototype.completeExtensions = function() {
    // this.extensions is a dict with entries like 'p' => { '[]' => false }, 'P'
    // => { '[0,1]' => true, '[1,1]' => false }, and 'f(a)' => 0. Let's turn
    // this into a complete list of extensions for all non-logical symbols,
    // i.e. this.predicates and this.origConstants.
    var result = {};
    for (var i=0; i<this.modelfinder.predicates.length; i++) {
        // Zero-ary predicates will have truth-values as extensions, one-ary
        // predicates list of individuals, other predicates lists of lists of
        // individuals.
        var pred = this.modelfinder.predicates[i];
        var ext = this.extensions[pred];
        if (!ext) {
            if (this.parser.arities[pred] == 0) result[pred] = false;
            else result[pred] = [];
        }
        else {
            result[pred] = [];
            var argumentLists = Object.keys(ext);
            for (var j=0; j<argumentLists.length; j++) {
                var args = argumentLists[j];
                if (this.parser.arities[pred] == 0) {
                    result[pred] = ext[args];
                }
                else if (ext[args]) { // only list positive extensions
                    args = args.slice(1,-1).split(',');
                    if (args.length == 1) result[pred].push(args[0]);
                    else result[pred].push(args);
                }
            }
        }
    }
    var interpretedExpressions = Object.keys(this.extensions);
    for (var i=0; i<this.modelfinder.origConstants.length; i++) {
        // Zero-ary constants will have individuals as extensions, others lists
        // of lists of individuals.
        var cons = this.modelfinder.origConstants[i];
        if (this.parser.arities[cons] == 0) {
            result[cons] = this.extensions[cons] || 0;
            continue;
        }
        // If cons is 'f', we have records in this.extensions for things like
        // '[f,0]' or '[f,a]' or '[f,[f,a]]'. We will then also have
        // records for the subterms.
        result[cons] = [];
        // log("constructing extension for "+cons+" (arity "+this.parser.arities[cons]+")");
        for (var j=0; j<interpretedExpressions.length; j++) {
            var expr = interpretedExpressions[j];
            if (expr.indexOf('['+cons+',') == 0) { // '[f,a]' or '[f,[f,a]]', etc.
                // log("   we know that "+expr+" = "+this.extensions[expr]);
                // replace complex arguments like '[f,a]' by their extension: 
                var expr2 = expr.slice(1,-1).replace(/(\[.+?\])/, this.extensions['$1'] || '0');
                // log("   subterms replaced: "+expr2);
                var args = expr2.split(',');
                args.shift(); 
                // convert simple arguments like 'a' to numbers:
                for (var k=0; k<args.length; k++) {
                    if (typeof args[k] != 'number') { 
                        args[k] = this.extensions[args[k]] || 0;
                    }
                }
                var value = this.extensions[expr];
                // log("   adding "+args+" => "+value);
                result[cons].push(args.concat([value]));
            }
        }
        // log("  "+result[cons]);
        // xxx make sure functions are total?
    }
    return result;
}

Model.prototype.classifyDomain = function() {
    // classify elements in the domain into worlds and individuals; create
    // domainWorlds and domainIndividuals attributes.

    // xxx
    this.domainIndividuals = [];
    this.domainWorlds = this.domain;
    return;
    
    
    this.domainWorlds = [];
    this.domainIndividuals = [];
    
    for (var i=0; i<this.symbols.length; i++) {
        var sym = this.symbols[i];
        if (!this.isPredicate[sym]) continue;
        var arity = this.parser.arities[sym];
        for (var j=0; j<this.argLists[sym].length; j++) {
            if (this.values[sym][j]) { // argLists[sym][j] is in extension of sym
                var world = this.argLists[sym][j].slice(1,-1).split(',').pop();
                this.domainWorlds.push(world);
            }
        }
    }
}

Model.prototype.toString = function() {
    // for debugging
    return this.toHTML().replace(/<.+?>/g, '');
}
