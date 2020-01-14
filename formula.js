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
    // check whether this formula can be unified with the argument formula.
    // Returns a (minimally) unifying substitution (that, if applied to both
    // formulas, yields the same formula) if one exists, otherwise false.  A
    // substitution is simply an array of terms, which is interpreted as arr[1]
    // -> arr[2], arr[3] -> arr[4], ... (arr[1], arr[3], etc.  are
    // variables). Warning: Don't confuse an empty unifier [] with false!
    //
    // The following algorithm is losely based on the one described in S.
    // Hölldobler, Logik und Logikprogrammierung, Synchron Verlag, Heidelberg
    // 2001, §4.5.
    //
    // Note that this only works for literals.  For quantified formulas one
    // would have to care about capturing by quantified variables, which would
    // complicate things a little.
    if (this.type != 'literal') return false;
    if (this.sub && !formula.sub) return false;
    if (this.sub) return this.sub.unify(formula.sub);
    if (this.predicate != formula.predicate) return false;
    if (this.terms.length != formula.terms.length) return false;
    // So we have two atomic formulas of the same arity. Now we walk through all
    // the pairs of terms.
    var unifier = [];
    var terms1 = this.terms.copyDeep(); // copy() doesn't suffice: see pel38 
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
        var t1Var = (t1[0] == 'ξ' || t1[0] == 'ζ');
        var t2Var = (t2[0] == 'ξ' || t2[0] == 'ζ');
        if (!t1Var && !t2Var) {
            // neither term is variable: unification failed
            log('no, neither term variable');
            return false;
        }
        if (!t1Var) {
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
    // returns an equivalent formula in negation normal form
    var op = this.operator || this.quantifier;
    if (!op) return this;
    switch (op) {
    case '∧' : case '∨' : {
        // |A&B| = |A|&|B|
        // |AvB| = |A|v|B|
        var sub1 = this.sub1.normalize();
        var sub2 = this.sub2.normalize();
        return new BinaryFormula(op, sub1, sub2);
    }
    case '→' : {
        // |A->B| = |~A|v|B|
        var sub1 = this.sub1.negate().normalize();
        var sub2 = this.sub2.normalize();
        return new BinaryFormula('∨', sub1, sub2);
    }
    case '↔' : {
        // |A<->B| = |A&B|v|~A&~B|
        var sub1 = new BinaryFormula('∧', this.sub1, this.sub2).normalize();
        var sub2 = new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate()).normalize();
        return new BinaryFormula('∨', sub1, sub2);
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
            var newOp = op2 == '∧' ? '∨' : '∧';
            return new BinaryFormula(newOp, sub1, sub2);
        }
        case '→' : {
            // |~(A->B)| = |A|&|~B|
            var sub1 = this.sub.sub1.normalize();
            var sub2 = this.sub.sub2.negate().normalize();
            return new BinaryFormula('∧', sub1, sub2);
        }
        case '↔' : {
            // |~(A<->B)| = |A&~B|v|~A&B|
            var sub1 = new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate()).normalize();
            var sub2 = new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2).normalize();
            return new BinaryFormula('∨', sub1, sub2);
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

Formula.prototype.alpha = function(n) {
    // return first/second subformula for sentree alpha expansion
    var f = this;
    if (f.operator == '∧') {
        return n == 1 ? f.sub1 : f.sub2;
    }
    // formula is negated
    if (f.sub.operator == '∨') {
        return n == 1 ? f.sub.sub1.negate() : f.sub.sub2.negate();
    }
    if (f.sub.operator == '→') {
        return n == 1 ? f.sub.sub1 : f.sub.sub2.negate();
    }
}

Formula.prototype.beta = function(n) {
    // return first/second subformula for sentree beta expansion
    var f = this;
    if (f.operator == '∨') {
        return n == 1 ? f.sub1 : f.sub2;
    }
    if (f.operator == '→') {
        return n == 1 ? f.sub1.negate() : f.sub2;
    }
    // We treat A <-> B as expanding to (A&B) | (~A&~B), and ~(A<->B) to
    // (A&~B) | (~A&B); these intermediate notes will be removed before
    // displaying trees.
    if (f.operator == '↔') {
        return n == 1 ? new BinaryFormula('∧', f.sub1, f.sub2) :
            new BinaryFormula('∧', f.sub1.negate(), f.sub2.negate())
    }
    // formula is negated
    if (f.sub.operator == '∧') {
        return n == 1 ? f.sub.sub1.negate() : f.sub.sub2.negate();
    }
    if (f.sub.operator == '↔') {
        return n == 1 ? new BinaryFormula('∧', f.sub.sub1, f.sub.sub2.negate()) :
            new BinaryFormula('∧', f.sub.sub1.negate(), f.sub.sub2)
    }
}

function AtomicFormula(predicate, terms) {
    this.type = 'literal';
    this.predicate = predicate;
    this.terms = terms; // a,b,f(a,g(c),d) => a,b,[f,a,[g,c],d]
    this.string = predicate + AtomicFormula.terms2string(terms);
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
    if (typeof(origTerm) == 'string' && this.string.indexOf(origTerm) == -1) {
        return this;
    }
    var newTerms = AtomicFormula.substituteInTerms(this.terms, origTerm, newTerm, shallow);
    if (!this.terms.equals(newTerms)) {
        return new AtomicFormula(this.predicate, newTerms);
    }
    else return this;
}

AtomicFormula.substituteInTerms = function(terms, origTerm, newTerm, shallow) {
    var newTerms = [];
    for (var i=0; i<terms.length; i++) {
        var term = terms[i];
        if (term == origTerm) newTerms.push(newTerm);
        else if (term.isArray && !shallow) {
            newTerms.push(AtomicFormula.substituteInTerms(term, origTerm, newTerm));
        }
        else newTerms.push(term);
    }
    return newTerms;
}

AtomicFormula.substituteInTerm = function(term, origTerm, newTerm) {
    if (term == origTerm) return newTerm;
    if (term.isArray) return AtomicFormula.substituteInTerms(term, origTerm, newTerm);
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
    this.string = '(' + sub1 + operator + sub2 + ')';
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
    this.type = operator == '□' ? 'modalGamma' : 'modalDelta';
    this.string = operator + sub;
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
    this.string = '¬' + sub;
}

NegatedFormula.computeType = function(sub) {
    if (sub.operator == '¬') return 'doublenegation';
    switch (sub.type) {
    case 'literal': { return 'literal'; }
    case 'alpha': { return 'beta'; }
    case 'beta': { return sub.operator == '↔' ? 'beta' : 'alpha'; }
    case 'gamma': { return 'delta'; }
    case 'delta': { return 'gamma'; }
    case 'modalGamma': { return 'modalBeta'; }
    case 'modalDelta': { return 'modalGamma'; }
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
