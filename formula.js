// Formula objects should be treated as immutable.

function Formula() {
    // not actually called, but you may pretend that NegatedFormula etc. are all
    // subclasses of Formula insofar as they inherit Formula.prototype.
}

Formula.prototype.toString = function() {
    return this.string;
}

Formula.prototype.equals = function(fla) {
    return this.string == fla.string;
}

Formula.prototype.negate = function() {
    return new NegatedFormula(this);
}

Formula.prototype.unify = function(formula) {
    // checks whether this formula can be unified with the argument formula.
    // Returns a (minimally) unifying substitution (that, if applied to both
    // formulas, yields the same formula) if one exists, otherwise false.
    // A substitution is simply an array of terms, which is interpreted as
    // arr[1] -> arr[2], arr[3] -> arr[4], ... (arr[1], arr[3], etc.
    // are variables). Warning: Don't confuse an empty unifier [] with false!
    //
    // The following algorithm is losely based on the one described in S.
    // Hölldobler, Logik und Logikprogrammierung, Synchron Verlag,
    // Heidelberg 2001, §4.5.
    //
    // Note that this only works for literals.  For quantified
    // formulas one would have to care about capturing by quantified
    // variables, which would complicate things a little.
    if (this.type != 'literal') return false;
    if (this.sub && !formula.sub) return false;
    if (this.sub) return this.sub.unify(formula.sub);
    if (this.predicate != formula.predicate) return false;
    if (this.terms.length != formula.terms.length) return false;
    // So we have two atomic formulas of the same arity. Now we walk through all
    // the pairs of terms.
    var unifier = [];
    var terms1 = this.terms.copyDeep(); // xxx wouldn't copy() suffice?
    var terms2 = formula.terms.copyDeep();
    var t1, t2;
    while (t1 = terms1.shift(), t2 = terms2.shift()) {
        log('unify terms? '+t1+' <=> '+t2);
        if (t1 == t2) {
            // terms are equal: nothing to do.
            continue;
        }
        if (t1.isArray && t2.isArray) {
            // both terms are functional: unification fails if function symbols
            // differ; otherwise add all the argument pairs to the terms that
            // must be unified.
            if (t1[0] != t2[0]) return false;
            for (var i=1; i<t1.length; i++) {
                terms1.push(t1[i]);
                terms2.push(t2[i]);
            }
            continue;
        }
        if (t1[0] != 'ξ' && t2[0] != 'ξ') {
            // neither term is variable: unification failed
            return false;
        }
        if (t1[0] != 'ξ') {
            // only second term is a variable: exchange it with first term, so
            // that in what follows the first term is always a variable.
            var temp = t1; t1 = t2; t2 = temp; 
        }
        if (t2.isArray) {
            // t2 is a function term: unification fails if it contains t1 among
            // its arguments (or arguments of its ... arguments).
            var terms, termss = [t2];
            while (terms = termss.shift()) {
                // log(terms);
                for (var i=0; i<terms.length; i++) {
                    if (terms[i].isArray) termss.push(terms[i]);
                    else if (terms[i] == t1) return false;
                }
            }
        }
        // now we unify the variable t1 with the term t2: substitute t2
        // for t1 everywhere in the unifier array and in the remaining
        // terms1 and terms2, and add t1/t2 to the unifier array.
        log('yes: unify');
        var terms, termss = [unifier, terms1, terms2];
        while (terms = termss.shift()) {
            for (var i=0; i<terms.length; i++) {
                if (terms[i].isArray) termss.push(terms[i]);
                else if (terms[i] == t1) terms[i] = t2;
            }
        }
        unifier.push(t1); unifier.push(t2);
    }
    return unifier;
}

Formula.prototype.normalize = function() {
    // returns an equivalent formula in negation normal form, in which left
    // subformulas are generally less complex than right subformulas (complexity
    // here means number of disjunctions). This helps when constructing proofs:
    // we can always focus on the leftmost open branch in a tree. xxx todo
    // implement, and see if it helps at all.
    var op = this.operator || this.quantifier;
    if (!op) return this;
    switch (op) {
    case '∧' : case '∨' : {
        // |A&B| = |A|&|B|
        // |AvB| = |A|v|B|
        return new BinaryFormula(op, this.sub1.normalize(), this.sub2.normalize());
    }
    case '→' : {
        // |A->B| = |~A|v|B|
        return new BinaryFormula('∨', this.sub1.negate().normalize(), this.sub2.normalize());
    }
    case '↔' : {
        // |A<->B| = |A&B|v|~A&~B|
        var sub1 = new BinaryFormula('∧', this.sub1, this.sub2);
        var sub2 = new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate());
        return new BinaryFormula('∨', sub1.normalize(), sub2.normalize());
    }
    case '∀' : case '∃' : {
        // |(Ax)A| = Ax|A|
        return new QuantifiedFormula(op, this.variable, this.matrix.normalize(),
                                     this.overWorlds);
    }
    case '□' : case '◇' : {
        // |[]A| = []|A|
        return new ModalFormula(op, this.sub.normalize());
    }
    case '¬' : {
        var op2 = this.sub.operator || this.sub.quantifier;
        if (!op2) return this;
        switch (op2) {
        case '∧' : case '∨' : {
            // |~(A&B)| = |~A|v|~B|
            // |~(AvB)| = |~A|&|~B|
            var sub1 = this.sub.sub1.negate().normalize();
            var sub2 = this.sub.sub2.negate().normalize();
            return new BinaryFormula(op2=='∧' ? '∨' : '∧', sub1, sub2);
        }
        case '→' : {
            // |~(A->B)| = |A|&|~B|
            var sub1 = this.sub.sub1.normalize();
            var sub2 = this.sub.sub2.negate().normalize();
            return new BinaryFormula('∧', sub1, sub2);
        }
        case '↔' : {
            // |~(A<->B)| = |A&~B|v|~A&B|
            var sub1 = new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate());
            var sub2 = new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2);
            return new BinaryFormula('∨', sub1.normalize(), sub2.normalize());
        }
        case '∀' : case '∃' : {
            // |~(Ax)A| = Ex|~A|
            var sub = this.sub.matrix.negate().normalize();
            return new QuantifiedFormula(op2=='∀' ? '∃' : '∀', this.sub.variable, sub,
                                         this.sub.overWorlds);
        }
        case '□' : case '◇' : {
            // |~[]A| = []|~A|
            var sub = this.sub.sub.negate().normalize();
            return new ModalFormula(op2=='□' ? '◇' : '□', sub);
        }
        case '¬' : {
            // |~~A| = |A|
            return this.sub.sub.normalize();
        }
        }
    }
    }
}

Formula.prototype.prenex = function() { // xxx unused
    // return formula with universal quantifiers moved to front; formula must be
    // skolemized and in NNF.
    if (this.sub1) { // ∀xP ∧ Q => ∀x(P ∧ Q), Q ∧ ∀xP => ∀x(Q ∧ P)
        var nsub1 = this.sub1.quantifier ? this.sub1.matrix.prenex() : this.sub1.prenex();
        var nsub2 = this.sub2.quantifier ? this.sub2.matrix.prenex() : this.sub2.prenex();
        if (this.sub1 == nsub1 && this.sub2 == nsub2) return this;
        var res = new BinaryFormula(this.operator, nsub1, nsub2);
        if (this.sub2.quantifier) {
            res = new QuantifiedFormula('∀', this.sub2.variable, res);
        }
        if (this.sub1.quantifier) {
            res = new QuantifiedFormula('∀', this.sub1.variable, res);
        }
        return res;
    }
    return this;
}


Formula.prototype.removeQuantifiers = function() {
    // return formula with all quantifiers removed; formula must be skolemized
    // and in NNF.
    if (this.matrix) return this.matrix.removeQuantifiers();
    if (this.sub1) {
        var nsub1 = this.sub1.quantifier ?
            this.sub1.matrix.removeQuantifiers() : this.sub1.removeQuantifiers();
        var nsub2 = this.sub2.quantifier ?
            this.sub2.matrix.removeQuantifiers() : this.sub2.removeQuantifiers();
        if (this.sub1 == nsub1 && this.sub2 == nsub2) return this;
        var res = new BinaryFormula(this.operator, nsub1, nsub2);
        return res;
    }
    return this;
}

// Formula.prototype.isModal = function() {
//     var fla, flas = [this];
//     while ((fla = flas.shift())) {
//         if (fla.operator == '□' || fla.operator == '◇') return true;
//         if (fla.matrix) {
//             flas.push(fla.matrix);
//         }
//         else if (fla.sub) {
//             flas.push(fla.sub);
//         }
//         else if (fla.sub1) {
//             flas.push(fla.sub1);
//             flas.push(fla.sub2);
//         }
//     }
//     return false;
// }

// Formula.prototype.getBoundVariables = function() {
//     // returns all bound variables in the formula (no duplicates)
//     var result = [];
//     var fla, flas = [this];
//     while ((fla = flas.shift())) {
//         if (fla.variable) {
//             if (!result.includes(fla.variable)) result.push(fla.variable);
//             flas.push(fla.matrix);
//         }
//         else if (fla.sub) {
//             flas.push(fla.sub);
//         }
//         else if (fla.sub1) {
//             flas.push(fla.sub1);
//             flas.push(fla.sub2);
//         }
//     }
//     return result;
// }

// Formula.prototype.getConstants = function(withArity) { 
//     // returns a list of all constants and function symbols in the (normalized)
//     // formula. If <withArity> is set and true, the returned elements are
//     // objects with properties 'constant' and 'arity'.
//     var result = [], resultWithArity = [];
//     var boundVars = []; // xxx check: what if a variable occurs both free and bound?
//     var fla, flas = [this];
//     while ((fla = flas.shift())) {
//         if (fla.matrix) {
//             flas.push(fla.matrix);
//             boundVars.push(fla.variable);
//             continue;
//         }
//         if (fla.sub1) {
//             flas.push(fla.sub1);
//             flas.push(fla.sub2);
//             continue;
//         }
//         if (fla.sub) {
//             flas.push(fla.sub);
//             continue;
//         }
//         var term, terms = fla.terms.copyDeep();
//         while ((term = terms.shift())) {
//             if (term.isArray) {
//                 for (var i=1; i<term.length; i++) terms.push(term[i]);
//                 if (result.includes(term[0])) continue;
//                 result.push(term[0]);
//                 if (withArity) {
//                     resultWithArity.push({ constant : term[0], arity : term.length-1 });
//                 }
//             }
//             else if (!result.includes(term) && !boundVars.includes(term)) {
//                 result.push(term);
//                 if (withArity) {
//                     resultWithArity.push({ constant : term, arity : 0 });
//                 }
//             }
//         }
//     }
//     return withArity ? resultWithArity : result;
// }

// Formula.prototype.getPredicates = function(withArity) {
//     // returns a list of all predicates in the formula. If <withArity>
//     // is set and true, the returned elements are objects with
//     // properties 'predicate' and 'arity'.
//     var result = [], resultWithArity = [];
//     var fla, flas = [this];
//     while ((fla = flas.shift())) {
//         if (fla.matrix) {
//             flas.push(fla.matrix);
//             continue;
//         }
//         if (fla.sub1) {
//             flas.push(fla.sub1);
//             flas.push(fla.sub2);
//             continue;
//         }
//         if (fla.sub) {
//             flas.push(fla.sub);
//             continue;
//         }
//         if (!result.includes(fla.predicate)) {
//             result.push(fla.predicate);
//             if (withArity) {
//                 resultWithArity.push({ predicate : fla.predicate, arity : fla.terms.length });
//             }
//         }
//     }
//     return withArity ? resultWithArity : result;
// }

Formula.prototype.alpha = function(n) {
    // return first/second formula for sentree alpha expansion
    if (this.operator == '∧') {
        return n == 1 ? this.sub1 : this.sub2;
    }
    // formula is negated
    if (this.sub.operator == '∨') {
        return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
    }
    if (this.sub.operator == '→') {
        return n == 1 ? this.sub.sub1 : this.sub.sub2.negate();
    }
}

Formula.prototype.beta = function(n) {
    // return first/second formula for sentree alpha expansion
    if (this.operator == '∨') {
        return n == 1 ? this.sub1 : this.sub2;
    }
    if (this.operator == '→') {
        return n == 1 ? this.sub1.negate() : this.sub2;
    }
    // We treat A <-> B as expanding to (A&B) | (~A&~B), and ~(A<->B) to
    // (A&~B) | (~A&B); these intermediate notes will be removed before
    // displaying trees.
    if (this.operator == '↔') {
        return n == 1 ? new BinaryFormula('∧', this.sub1, this.sub2) :
            new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate())
    }
    // formula is negated
    if (this.sub.operator == '∧') {
        return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
    }
    if (this.sub.operator == '↔') {
        return n == 1 ? new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate()) :
            new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2)
    }
}

function AtomicFormula(predicate, terms) {
    this.type = 'literal';
    this.predicate = predicate;
    this.terms = terms; // a,b,f(a,g(c),d) => a,b,[f,a,[g,c],d]
    this.string = this.predicate + AtomicFormula.terms2string(this.terms);
    this.predicates = [predicate];
    // this.constants = []; // includes function symbols
    this.variables = [];
    // classify atomic terms into variables and constants:
    // var list = terms;
    // for (var i=0; i<list.length; i++) {
    //     if (list[i].isArray) list = list.concat(list[i]);
    //     else {
    //         var termType = this.parser.expressionType[list[i]];
    //         if (termType == 'variable' || termType == 'world variable') {
    //             this.variables.pushNoDuplicates(list[i]);
    //         }
    //         else this.constants.pushNoDuplicates(list[i]);
    //     }
    // }
    // if (this.parser.isPropositional &&
    //     this.terms.length > 0 &&
    //     (!this.parser.isModal ||
    //      (this.predicate != this.parser.R && this.terms.length > 1))) {
    //         this.parser.isPropositional = false;
    // }
    // log(this.constants);
}

AtomicFormula.terms2string = function(list) {
    var res = '';
    for (var i=0; i<list.length; i++) {
        if (list[i].isArray) {
            var sublist = list[i].copy();
            var funcsym = sublist.shift();
            res += funcsym+'('+AtomicFormula.terms2string(sublist)+')';
        }
        else res += list[i];
    }
    return res;
}

AtomicFormula.prototype = Object.create(Formula.prototype);

AtomicFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var newTerms = [];
    for (var i=0; i<this.terms.length; i++) {
        newTerms.push(AtomicFormula.substituteInTerm(this.terms[i], origTerm, newTerm, shallow));
    }
    if (!this.terms.equals(newTerms)) {
        return new AtomicFormula(this.predicate, newTerms);
    }
    else return this;
}
AtomicFormula.substituteInTerm = function(term, origTerm, newTerm, shallow) {
    // xxx this could be optimized (it's also used in prover)
    if (term.isArray && !shallow) {
        var nTerm = [];
        for (var i=0; i<term.length; i++) {
            nTerm.push(AtomicFormula.substituteInTerm(term[i], origTerm, newTerm));
        }
        return nTerm;
    }
    if (term == origTerm) return newTerm;
    return term;
}

function QuantifiedFormula(quantifier, variable, matrix, overWorlds) {
    this.quantifier = quantifier;
    this.variable = variable;
    this.matrix = matrix;
    this.overWorlds = overWorlds;
    if (overWorlds) {
        this.type = quantifier == '∀' ? 'modalGamma' : 'modalDelta';
    }
    else {
        this.type = quantifier == '∀' ? 'gamma' : 'delta';
    }
    this.string = quantifier + variable + matrix;
    this.predicates = matrix.predicates;
    // this.constants = matrix.constants;
    // this.variables = matrix.variables; // if current variable is vacuous we
                                       // don't care if it's listed under
                                       // variables
    
    // We could now set this.parser.isPropositional = false, so that ∀xP counts
    // as a non-propositional formula; OTOH, it's useful to have
    // parser.isPropositional true for modal formulas. So we only set
    // parser.isPropositional in AtomicFormula and treat ∀xP as propositional.
}

QuantifiedFormula.prototype = Object.create(Formula.prototype);

QuantifiedFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    if (this.variable == origTerm) return this;
    var nmatrix = this.matrix.substitute(origTerm, newTerm, shallow);
    if (nmatrix == this.matrix) return this;
    return new QuantifiedFormula(this.quantifier, this.variable, nmatrix, this.overWorlds);
}

function BinaryFormula(operator, sub1, sub2) {
    this.operator = operator;
    this.sub1 = sub1;
    this.sub2 = sub2;
    this.type = operator == '∧' ? 'alpha' : 'beta';
    this.string = '(' + this.sub1 + this.operator + this.sub2 + ')';
    this.predicates = this.sub1.predicates.copy();
    // xxx optimize the following by defining Array.merge?
    for (var i=0; i<this.sub2.predicates.length; i++) {
        var pred = this.sub2.predicates[i];
        if (!this.predicates.includes(pred)) {
            this.predicates.push(pred);
        }
    }
    // this.constants = this.sub1.constants.copy();
    // for (var i=0; i<this.sub2.constants.length; i++) {
    //     var cons = this.sub2.constants[i];
    //     if (!this.constants.includes(cons)) {
    //         this.constants.push(cons);
    //     }
    // }
    // this.variables = this.sub1.variables.copy();
    // for (var i=0; i<this.sub2.variables.length; i++) {
    //     var vari = this.sub2.variables[i];
    //     if (!this.variables.includes(vari)) {
    //         this.variables.push(vari);
    //     }
    // }
}

BinaryFormula.prototype = Object.create(Formula.prototype);

BinaryFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var nsub1 = this.sub1.substitute(origTerm, newTerm, shallow);
    var nsub2 = this.sub2.substitute(origTerm, newTerm, shallow);
    if (this.sub1 == nsub1 && this.sub2 == nsub2) return this;
    return new BinaryFormula(this.operator, nsub1, nsub2);
}

function ModalFormula(operator, sub) {
    this.operator = operator;
    this.sub = sub;
    this.type = operator == '□' ? 'boxy' : 'diamondy';
    this.string = this.operator + this.sub;
    this.predicates = this.sub.predicates;
    // this.constants = this.sub.constants;
    // this.variables = this.sub.variables;
}

ModalFormula.prototype = Object.create(Formula.prototype);

ModalFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var nsub = this.sub.substitute(origTerm, newTerm, shallow);
    if (this.sub == nsub) return this;
    return new ModalFormula(this.operator, nsub);
}

function NegatedFormula(sub) {
    this.operator = '¬';
    this.sub = sub;
    this.type = NegatedFormula.computeType(sub);
    this.string = '¬' + this.sub;
    this.predicates = this.sub.predicates;
    // this.constants = this.sub.constants;
    // this.variables = this.sub.variables;
}

NegatedFormula.computeType = function(sub) {
    if (sub.operator == '¬') return 'doublenegation';
    switch (sub.type) {
    case 'literal': { return 'literal'; }
    case 'alpha': { return 'beta'; }
    case 'beta': { return sub.operator == '↔' ? 'beta' : 'alpha'; }
    case 'gamma': { return 'delta'; }
    case 'delta': { return 'gamma'; }
    case 'boxy': { return 'diamondy'; }
    case 'diamondy': { return 'boxy'; }
    }
}

NegatedFormula.prototype = Object.create(Formula.prototype);

NegatedFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var nsub = this.sub.substitute(origTerm, newTerm, shallow);
    if (this.sub == nsub) return this;
    return new NegatedFormula(nsub);
}

