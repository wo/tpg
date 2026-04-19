
// Helper: create a ModelFinder and return its model with grounding complete.
// formulas can be a single string or array of strings.
// domainSize defaults to 1 (uses mf.model); pass >1 to create a new Model.
function getModel(formulas, domainSize) {
    var parser = new Parser();
    if (typeof formulas === 'string') formulas = [formulas];
    var parsed = formulas.map(function(f) { return parser.parseFormula(f); });
    var mf = new ModelFinder(parsed, parser);
    var m;
    if (domainSize && domainSize > 1) {
        m = new Model(mf, domainSize, 0);
    } else {
        m = mf.model;
    }
    m.groundIncremental(Infinity);
    return m;
}

tests = {

    // ============================================================
    // Cell creation
    // ============================================================

    createCells_proposition: function() {
        // Proposition letter p: one cell 'p[]' with possible [true, false]
        // Use p∨q so that p[] is not forced by a unit clause during grounding
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p∨q')], parser);
        var m = mf.model;
        var cell = m.cellIndex['p[]'];
        assert(cell);
        assertEqual(cell.isFunction, false);
        assertEqual(cell.possible.length, 2);
        assertEqual(cell.value, null);
    },

    createCells_constant: function() {
        // Constant a: one cell 'a' with possible = domain
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Fa')], parser);
        var m = mf.model;
        var cell = m.cellIndex['a'];
        assert(cell);
        assertEqual(cell.isFunction, true);
        assertEqual(cell.possible.toString(), '[0]'); // domain {0}
    },

    createCells_predicate: function() {
        // Unary predicate F on domain {0}: one cell 'F[0]'
        // Use Fx∨Gx so F[0] is not forced by a unit clause
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀x(Fx∨Gx)')], parser);
        var m = mf.model;
        var cell = m.cellIndex['F[0]'];
        assert(cell);
        assertEqual(cell.isFunction, false);
        assertEqual(cell.possible.toString(), '[false,true]');
    },

    createCells_predicate_domain2: function() {
        // Unary predicate F on domain {0,1}: cells 'F[0]' and 'F[1]'
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀xFx')], parser);
        var m = new Model(mf, 2, 0);
        assert(m.cellIndex['F[0]']);
        assert(m.cellIndex['F[1]']);
    },

    createCells_binary_predicate: function() {
        // Binary predicate R on domain {0,1}: 4 cells
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀x∀yRxy')], parser);
        var m = new Model(mf, 2, 0);
        assert(m.cellIndex['R[0,0]']);
        assert(m.cellIndex['R[0,1]']);
        assert(m.cellIndex['R[1,0]']);
        assert(m.cellIndex['R[1,1]']);
    },

    createCells_function: function() {
        // Unary function f on domain {0,1}: cells '[f,0]' and '[f,1]'
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a)')], parser);
        var m = new Model(mf, 2, 0);
        assert(m.cellIndex['[f,0]']);
        assert(m.cellIndex['[f,1]']);
        assertEqual(m.cellIndex['[f,0]'].isFunction, true);
        assertEqual(m.cellIndex['[f,0]'].possible.toString(), '[0,1]');
    },

    createCells_equality: function() {
        // Equality cells on domain {0,1}: =[0,0]=true, =[0,1]=false, etc.
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('a=a')], parser);
        var m = new Model(mf, 2, 0);
        var eq00 = m.cellIndex['=[0,0]'];
        var eq01 = m.cellIndex['=[0,1]'];
        if (eq00) {
            assertEqual(eq00.fixed, true);
            assertEqual(eq00.value, true);
        }
        if (eq01) {
            assertEqual(eq01.fixed, true);
            assertEqual(eq01.value, false);
        }
    },

    // ============================================================
    // Ground clause building and occurrence index
    // ============================================================

    buildGroundClauses_simple: function() {
        // Formula: ∀xFx on domain {0} => one ground clause [F0]
        var m = getModel('∀xFx');
        assertEqual(m.groundClauses.length, 1);
        assertEqual(m.groundClauses[0].literals.length, 1);
        assertEqual(m.groundClauses[0].literals[0].predicate, 'F');
        assertEqual(m.groundClauses[0].literals[0].positive, true);
    },

    buildGroundClauses_negated: function() {
        // Formula: ¬p => one ground clause [¬p]
        var m = getModel('¬p');
        assertEqual(m.groundClauses.length, 1);
        assertEqual(m.groundClauses[0].literals[0].positive, false);
        assertEqual(m.groundClauses[0].literals[0].predicate, 'p');
    },

    buildGroundClauses_occurrences_ground_predicate: function() {
        // ∀xFx on domain {0}: literal F0 has terms [0], which are all numbers.
        // So occurrence should be registered on cell 'F[0]'.
        var m = getModel('∀xFx');
        var cell = m.cellIndex['F[0]'];
        assert(cell);
        assert(cell.occurrences.length >= 1);
    },

    buildGroundClauses_occurrences_with_constant: function() {
        // Formula: Fa on domain {0}.
        // Literal has terms ['a']. The constant cell 'a' should have an occurrence.
        var m = getModel('Fa');
        var aCell = m.cellIndex['a'];
        assert(aCell);
        assert(aCell.occurrences.length >= 1);
    },

    buildGroundClauses_occurrences_with_function: function() {
        // Formula: Ff(a) on domain {0}.
        // Terms: [['f','a']].
        // Function cell '[f,0]' or constant cell 'a' should have occurrences.
        var m = getModel('Ff(a)');
        var aCell = m.cellIndex['a'];
        assert(aCell);
        assert(aCell.occurrences.length >= 1, 'constant a should have occurrence');
    },

    buildGroundClauses_multiple_clauses: function() {
        // ∀xFx on domain {0,1}: two unit clauses [F0], [F1]
        var m = getModel('∀xFx', 2);
        // Should have at least 2 ground clauses for F0 and F1
        var fClauses = m.groundClauses.filter(function(gc) {
            return gc.literals.some(function(l) { return l.predicate === 'F'; });
        });
        assert(fClauses.length >= 2);
    },

    // ============================================================
    // reduceTermFromCells
    // ============================================================

    reduceTermFromCells_number: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Fa')], parser);
        var m = mf.model;
        assertEqual(m.reduceTermFromCells(0), 0);
        assertEqual(m.reduceTermFromCells(1), 1);
    },

    reduceTermFromCells_constant_unassigned: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Fa')], parser);
        var m = mf.model;
        assertEqual(m.reduceTermFromCells('a'), 'a');
    },

    reduceTermFromCells_constant_assigned: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Fa')], parser);
        var m = mf.model;
        m.cellIndex['a'].value = 0;
        assertEqual(m.reduceTermFromCells('a'), 0);
    },

    reduceTermFromCells_function_term: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a)')], parser);
        var m = new Model(mf, 2, 0);
        // With a=0 and f(0)=1:
        m.cellIndex['a'].value = 0;
        m.cellIndex['[f,0]'].value = 1;
        var result = m.reduceTermFromCells(['f', 'a']);
        assertEqual(result, 1);
    },

    reduceTermFromCells_nested: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(f(a))')], parser);
        var m = new Model(mf, 2, 0);
        m.cellIndex['a'].value = 0;
        m.cellIndex['[f,0]'].value = 1;
        m.cellIndex['[f,1]'].value = 0;
        // f(f(a)) = f(f(0)) = f(1) = 0
        var result = m.reduceTermFromCells(['f', ['f', 'a']]);
        assertEqual(result, 0);
    },

    reduceTermFromCells_partial: function() {
        // With a=0 but f(0) unassigned: f(a) should reduce to ['f',0]
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a)')], parser);
        var m = new Model(mf, 2, 0);
        m.cellIndex['a'].value = 0;
        var result = m.reduceTermFromCells(['f', 'a']);
        // Should be the array ['f', 0] (not fully reduced)
        assert(result.isArray);
        assertEqual(result[0], 'f');
        assertEqual(result[1], 0);
    },

    // ============================================================
    // evaluateLiteral
    // ============================================================

    evaluateLiteral_indeterminate: function() {
        // F0 with F[0] unassigned => null
        // Use Fx∨Gx so F[0] is not forced during grounding
        var m = getModel('∀x(Fx∨Gx)');
        // Find the F literal:
        var lit = null;
        for (var i=0; i<m.groundClauses.length; i++) {
            for (var j=0; j<m.groundClauses[i].literals.length; j++) {
                if (m.groundClauses[i].literals[j].predicate === 'F') {
                    lit = m.groundClauses[i].literals[j];
                }
            }
        }
        assert(lit);
        assertEqual(m.evaluateLiteral(lit), null);
    },

    evaluateLiteral_true: function() {
        // F0 with F[0]=true => true
        var m = getModel('∀xFx');
        m.cellIndex['F[0]'].value = true;
        var lit = m.groundClauses[0].literals[0];
        assertEqual(m.evaluateLiteral(lit), true);
    },

    evaluateLiteral_false: function() {
        // F0 with F[0]=false => false
        var m = getModel('∀xFx');
        m.cellIndex['F[0]'].value = false;
        var lit = m.groundClauses[0].literals[0];
        assertEqual(m.evaluateLiteral(lit), false);
    },

    evaluateLiteral_negated_true: function() {
        // ¬∀xFx => ∃x¬Fx => skolemized ¬Fa. Terms contain constant 'a'.
        // After assigning a=0 and F[0]=false, the literal ¬Fa should evaluate
        // to true.
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬∀xFx').nnf()], parser);
        var m = mf.model;
        m.groundIncremental(Infinity);
        var lit = null;
        for (var i=0; i<m.groundClauses.length; i++) {
            for (var j=0; j<m.groundClauses[i].literals.length; j++) {
                if (m.groundClauses[i].literals[j].predicate === 'F') {
                    lit = m.groundClauses[i].literals[j];
                }
            }
        }
        assert(lit);
        assertEqual(lit.positive, false);
        // Before assigning a, literal is indeterminate:
        assertEqual(m.evaluateLiteral(lit), null);
        // After assigning a=0 and F[0]=false:
        m.cellIndex['a'].value = 0;
        m.cellIndex['F[0]'].value = false;
        assertEqual(m.evaluateLiteral(lit), true);
    },

    evaluateLiteral_with_constant: function() {
        // Fa with a unassigned => null (terms contain 'a', not a number)
        var m = getModel('Fa');
        var lit = m.groundClauses[0].literals[0];
        assertEqual(m.evaluateLiteral(lit), null);
    },

    evaluateLiteral_with_constant_assigned: function() {
        // Fa with a=0, F[0]=true => true
        var m = getModel('Fa');
        m.cellIndex['a'].value = 0;
        m.cellIndex['F[0]'].value = true;
        var lit = m.groundClauses[0].literals[0];
        assertEqual(m.evaluateLiteral(lit), true);
    },

    // ============================================================
    // Trail and undo
    // ============================================================

    trail_assign_undo: function() {
        // Use Fx∨Gx so F[0] is not forced during grounding
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀x(Fx∨Gx)')], parser);
        var m = mf.model;
        var cell = m.cellIndex['F[0]'];
        var mark = m.trail.length;
        m.trail.push({type: 'assign', cell: cell, oldPossible: cell.possible.slice()});
        cell.value = true;
        cell.possible = [];
        assertEqual(cell.value, true);
        m.undoToMark(mark);
        assertEqual(cell.value, null);
        assertEqual(cell.possible.length, 2);
    },

    trail_satisfy_undo: function() {
        var m = getModel('∀xFx');
        var gc = m.groundClauses[0];
        var mark = m.trail.length;
        m.trail.push({type: 'satisfy', clause: gc});
        gc.satisfied = true;
        m.undoToMark(mark);
        assertEqual(gc.satisfied, false);
    },

    trail_deactivate_undo: function() {
        var m = getModel('p∨q');
        var gc = m.groundClauses[0];
        assertEqual(gc.numActive, 2);
        var mark = m.trail.length;
        m.trail.push({type: 'deactivate', clause: gc, litIdx: 0});
        gc.literals[0].active = false;
        gc.numActive--;
        assertEqual(gc.numActive, 1);
        m.undoToMark(mark);
        assertEqual(gc.numActive, 2);
        assertEqual(gc.literals[0].active, true);
    },

    // ============================================================
    // assignCell and propagation
    // ============================================================

    assignCell_simple: function() {
        // Assign F[0]=true for clause [F0]: should satisfy the clause
        var m = getModel('∀xFx');
        var cell = m.cellIndex['F[0]'];
        var ok = m.assignCell(cell, true);
        assertEqual(ok, true);
        assertEqual(cell.value, true);
        assertEqual(m.groundClauses[0].satisfied, true);
    },

    assignCell_contradiction: function() {
        // (p∨q) ∧ (¬p∨¬q) ∧ (p∨¬q) ∧ (¬p∨q): unsatisfiable but not
        // detected at grounding. Assigning p=true, q=true contradicts clause 2.
        var m = getModel(['p∨q', '¬p∨¬q', 'p∨¬q', '¬p∨q']);
        var pCell = m.cellIndex['p[]'];
        // Assigning p=true forces q=true (from clause 4: ¬p∨q), which
        // contradicts clause 2 (¬p∨¬q becomes ¬q which is false).
        var ok = m.assignCell(pCell, true);
        assertEqual(ok, false);
    },

    assignCell_unit_propagation: function() {
        // Clauses: [p], [¬p, q]. Assigning p[]=true should satisfy [p],
        // falsify ¬p in [¬p,q], making [q] a unit clause, forcing q[]=true.
        var m = getModel(['p', 'p→q']);
        var pCell = m.cellIndex['p[]'];
        var qCell = m.cellIndex['q[]'];
        assert(pCell);
        assert(qCell);
        var ok = m.assignCell(pCell, true);
        assertEqual(ok, true);
        assertEqual(qCell.value, true);
    },

    // ============================================================
    // selectCell
    // ============================================================

    selectCell_returns_unassigned: function() {
        var m = getModel(['p∨q', 'r∨s']);
        var cell = m.selectCell();
        assert(cell);
        assertEqual(cell.value, null);
    },

    selectCell_skips_assigned: function() {
        var m = getModel(['p∨q', 'r∨s']);
        // Assign all cells that appear in the first clause:
        m.cellIndex['p[]'].value = true;
        m.cellIndex['p[]'].possible = [];
        m.cellIndex['q[]'].value = true;
        m.cellIndex['q[]'].possible = [];
        var cell = m.selectCell();
        assert(cell);
        assert(cell.id === 'r[]' || cell.id === 's[]');
    },

    selectCell_returns_null_when_all_assigned: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p')], parser);
        var m = mf.model;
        m.cellIndex['p[]'].value = true;
        m.cellIndex['p[]'].possible = [];
        var cell = m.selectCell();
        assertEqual(cell, null);
    },

    // ============================================================
    // getCellValues with LNH
    // ============================================================

    getCellValues_predicate: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p∨q')], parser);
        var m = mf.model;
        var values = m.getCellValues(m.cellIndex['p[]']);
        assertEqual(values.toString(), '[false,true]');
    },

    getCellValues_constant: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Fa')], parser);
        var m = new Model(mf, 2, 0);
        var values = m.getCellValues(m.cellIndex['a']);
        // LNH: first constant always denotes 0
        assertEqual(values.toString(), '[0]');
    },

    // ============================================================
    // initialPropagation
    // ============================================================

    groundAndSimplify_unit_clause: function() {
        // ∀xFx on domain {0}: unit clause [F0] forces F[0]=true during grounding
        var m = getModel('∀xFx');
        assertEqual(m.initOk, true);
        assertEqual(m.cellIndex['F[0]'].value, true);
    },

    groundAndSimplify_contradiction: function() {
        // p ∧ ¬p: contradiction detected during grounding
        var m = getModel(['p', '¬p']);
        assertEqual(m.initOk, false);
    },

    groundAndSimplify_chain: function() {
        // [p], [¬p, q], [¬q, r]: should propagate p=true, then q=true, then r=true
        var m = getModel(['p', 'p→q', 'q→r']);
        assertEqual(m.initOk, true);
        assertEqual(m.cellIndex['p[]'].value, true);
        assertEqual(m.cellIndex['q[]'].value, true);
        assertEqual(m.cellIndex['r[]'].value, true);
    },

    // ============================================================
    // buildInterpretation
    // ============================================================

    buildInterpretation_basic: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('¬q')], parser);
        var m = mf.model;
        m.cellIndex['p[]'].value = true;
        m.cellIndex['q[]'].value = false;
        m.buildInterpretation();
        assertEqual(m.interpretation['p[]'], true);
        assertEqual(m.interpretation['q[]'], false);
    },

    // ============================================================
    // Modal: world constants and world function symbols get cells
    // ============================================================

    createCells_world_constant: function() {
        // In modal logic, world constants (like 'w' and skolem world
        // constants) should get cells with possible values = worlds domain.
        var parser = new Parser();
        var f1 = parser.parseFormula('◇p');
        var f2 = parser.parseFormula('¬p');
        var fs = [parser.translateFromModal(f1).nnf(), parser.translateFromModal(f2).nnf()];
        var mf = new ModelFinder(fs, parser);
        var wCell = mf.model.cellIndex['w'];
        assert(wCell, 'world constant w should have a cell');
        assertEqual(wCell.isFunction, true);
        // 'u' is a skolem world constant introduced during clausification
        var uCell = mf.model.cellIndex['u'];
        assert(uCell, 'skolem world constant u should have a cell');
        assertEqual(uCell.isFunction, true);
    },

    // ============================================================
    // Dynamic occurrence registration (cascading cell dependencies)
    // ============================================================

    propagation_constant_to_predicate: function() {
        // Fa on domain {0}: assigning a=0 should make literal Fa depend on
        // F[0]. Then assigning F[0]=true should satisfy the clause.
        var m = getModel('Fa');
        var aCell = m.cellIndex['a'];
        var fCell = m.cellIndex['F[0]'];
        // After assigning a=0, F[0] should gain an occurrence for this literal:
        var ok = m.assignCell(aCell, 0);
        assertEqual(ok, true);
        assert(fCell.occurrences.length >= 1,
               'F[0] should have occurrence after a=0 reveals dependency');
        // Now assigning F[0]=true should satisfy the clause:
        ok = m.assignCell(fCell, true);
        assertEqual(ok, true);
        assertEqual(m.groundClauses[0].satisfied, true);
    },

    propagation_function_chain: function() {
        // Ff(a) on domain {0,1}: assigning a=0 should make f(a) reduce to
        // [f,0], registering on cell [f,0]. Then assigning [f,0]=1 should
        // make the literal depend on F[1].
        var m = getModel('Ff(a)', 2);
        var aCell = m.cellIndex['a'];
        var f0Cell = m.cellIndex['[f,0]'];
        var F1Cell = m.cellIndex['F[1]'];
        // Assign a=0:
        m.assignCell(aCell, 0);
        assert(f0Cell.occurrences.length >= 1,
               '[f,0] should have occurrence after a=0');
        // Assign f(0)=1:
        m.assignCell(f0Cell, 1);
        assert(F1Cell.occurrences.length >= 1,
               'F[1] should have occurrence after f(0)=1');
    },

    propagation_nested_function: function() {
        // Ff(f(a)) on domain {0,1}: full chain a->f(0)->f(v)->F[w]
        // With eager propagation, assigning a=0, f(0)=1, f(1)=0 resolves
        // f(f(a))=f(1)=0, and the unit clause forces F[0]=true.
        var m = getModel('Ff(f(a))', 2);
        m.assignCell(m.cellIndex['a'], 0);
        m.assignCell(m.cellIndex['[f,0]'], 1);
        m.assignCell(m.cellIndex['[f,1]'], 0);
        assertEqual(m.cellIndex['F[0]'].value, true);
    },

    // ============================================================
    // Domain increase when no model at current size
    // ============================================================

    e2e_needs_domain2: function() {
        // Fa ∧ ¬Fb requires domain size >= 2 (a≠b)
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Fa ∧ ¬Fb')], parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 100, 'should find model');
        assertEqual(mf.model.domain.length, 2);
    },

    // ============================================================
    // Countermodel validation
    // ============================================================

    verify_countermodel_valid: function() {
        // (∃xFx→∃xGx)→∀x(Fx→Gx) is invalid; found model must satisfy
        // the negation.
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('(∃xFx→∃xGx)→∀x(Fx→Gx)').negate().nnf()], parser);
        for (var i=0; i<800; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 800, 'should find countermodel');
        assert(mf.model.verifyModel(), 'countermodel should satisfy all ground clauses');
    },

    verify_countermodel_minimal_extension: function() {
        // The countermodel for (∃xFx→∃xGx)→∀x(Fx→Gx) should prefer
        // minimal predicate extensions (try false before true).
        // Minimal: F={1}, G={0} (one element each) rather than F={0,1}, G={0}.
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('(∃xFx→∃xGx)→∀x(Fx→Gx)').negate().nnf()], parser);
        for (var i=0; i<800; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 800);
        assert(mf.model.toString().indexOf('F: { 1 }') > 0,
               'F should have minimal extension; got: ' + mf.model.toString());
        assert(mf.model.toString().indexOf('G: { 0 }') > 0,
               'G should have minimal extension; got: ' + mf.model.toString());
    },

    // ============================================================
    // End-to-end: full model finding via nextStep
    // ============================================================

    e2e_proposition_true: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p')], parser);
        for (var i=0; i<10; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 10);
        assertEqual(mf.model.toString().trim(), 'p: true');
    },

    e2e_proposition_false: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬p')], parser);
        for (var i=0; i<10; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 10);
        assertEqual(mf.model.toString().trim(), 'p: false');
    },

    e2e_two_propositions: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('¬q')], parser);
        for (var i=0; i<20; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 20);
        assertEqual(mf.model.toString().trim(), 'p: true\nq: false');
    },

    // =============================================================

    setup: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('Ff(a,a)')], parser);
        assert(mf.predicates.equals(['p','F']));
        assertEqual(mf.constants.toString(), '[a]');
        assertEqual(mf.funcSymbols.toString(), '[f]');
        assertEqual(mf.model.domain.length, 1);
        assertEqual(mf.model.worlds.length, 0);
    },

    skolemize: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('∀x∃y(Fx∧∀zHxyz)');
        f = f.nnf();
        var sk = mf.skolemize(f);
        assertEqual(sk.toString(), '∀x(Fx ∧ ∀zHxf(x)z)');
    },
    
    skolemize2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('∀x∃y∃zHxyz ∨ ∃v∀wGvw');
        f = f.nnf();
        var sk = mf.skolemize(f);
        assertEqual(sk.string, '(∀xHxf(x)g(x) ∨ ∀wGaw)');
    },

    cnf_basic: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.cnf(parser.parseFormula('p'));
        assertEqual(cnf.toString(), '[[p]]');
        var cnf = m.cnf(parser.parseFormula('¬p'));
        assertEqual(cnf.toString(), '[[¬p]]');
        var cnf = m.cnf(parser.parseFormula('p∨q'));
        assertEqual(cnf.toString(), '[[p,q]]');
        var cnf = m.cnf(parser.parseFormula('p∧q'));
        assertEqual(cnf.toString(), '[[p],[q]]');
        var cnf = m.cnf(parser.parseFormula('p→q'));
        assertEqual(cnf.toString(), '[[q,¬p]]');
        var cnf = m.cnf(parser.parseFormula('p↔q'));
        assertEqual(cnf.toString(), '[[q,¬p],[p,¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p∨q)'));
        assertEqual(cnf.toString(), '[[¬p],[¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p∧q)'));
        assertEqual(cnf.toString(), '[[¬p,¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p→q)'));
        assertEqual(cnf.toString(), '[[p],[¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p↔q)'));
        assertEqual(cnf.toString(), '[[p,q],[¬p,¬q]]');

        var cnf = m.cnf(parser.parseFormula('¬¬p'));
        assertEqual(cnf.toString(), '[[p]]');
    },

    cnf_sort_and_simplify: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.cnf(parser.parseFormula('(p∨p)'));
        assertEqual(cnf.toString(), '[[p]]');
        var cnf = m.cnf(parser.parseFormula('(p∨q)∧(p∨q)'));
        assertEqual(cnf.toString(), '[[p,q]]');
        var cnf = m.cnf(parser.parseFormula('(p∨q)∧(q∨p)'));
        assertEqual(cnf.toString(), '[[p,q]]');
        var cnf = m.cnf(parser.parseFormula('(p∨q)∧(q∨p∨q)'));
        assertEqual(cnf.toString(), '[[p,q]]');
    },
    
    cnf1: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.cnf(parser.parseFormula('((a∧b)∨(c∧d))∨e'));
        assertEqual(cnf.toString(), '[[a,c,e],[a,d,e],[b,c,e],[b,d,e]]');
    },

    cnf2: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('((¬F∨G)∧(B∧¬W))∨((C∧¬E)∧(¬T∨D))');
        var cnf = m.cnf(f);
        // wolframalpha: CNF (((~F || G) && (B && ~W)) || ((C && ~E) && (~T || D)))
        // var correct = '[[¬F,G,C],[¬F,G,¬E],[¬F,G,¬T,D],[B,C],[B,¬E],[B,¬T,D],[¬W,C],[¬W,¬E],[¬W,¬T,D]]';
        var correct = '[[C,G,¬F],[G,¬E,¬F],[D,G,¬F,¬T],[B,C],[B,¬E],[B,D,¬T],[C,¬W],[¬E,¬W],[D,¬T,¬W]]';
        assertEqual(cnf.toString(), correct);
    },

    cnf3: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula("(¬Px∨((¬Py∨Pf(xy))∧(Qxg(x)∧(¬Pg(x)∨¬Rcg(x)))))");
        var cnf = m.cnf(f);
        assertEqual(cnf.toString(), '[[Pf(x,y),¬Px,¬Py],[Qxg(x),¬Px],[¬Pg(x),¬Px,¬Rcg(x)]]');
    },

    cnfbicond: function(){
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('r ↔ (p↔q)');
        var cnf = m.cnf(f);
        assertEqual(cnf.toString(), '[[q,¬p,¬r],[p,¬q,¬r],[p,q,r],[r,¬p,¬q]]');
    },

    tseitinCNF_basic: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.tseitinCNF(parser.parseFormula('p'));
        assertEqual(cnf.toString(), '[[p]]');
        var cnf = m.tseitinCNF(parser.parseFormula('¬p'));
        assertEqual(cnf.toString(), '[[¬p]]');
        var cnf = m.tseitinCNF(parser.parseFormula('p∨q'));
        assertEqual(cnf.toString(), '[[$],[$,¬p],[$,¬q],[p,q,¬$]]');
        var cnf = m.tseitinCNF(parser.parseFormula('p∧q'));
        assertEqual(cnf.toString(), '[[p],[q]]');
        // assertEqual(cnf.toString(), '[[$2],[p,¬$2],[q,¬$2],[$2,¬p,¬q]]');
    },
    
    // transformations2: function() {
    //     // example from http://www8.cs.umu.se/kurser/TDBB08/vt98b/Slides4/norm1_4.pdf
    //     var parser = new Parser();
    //     var f = parser.parseFormula('∀x(Px→(∀y(Py→Pf(x,y)))∧¬∀y(Qxy→(Py∧Rcy)))');
    //     f = f.nnf();
    //     var mf = new ModelFinder([f], parser);
    //     var cnf = mf.clauses;
    //     assertEqual(cnf.toString(), '[[¬Px,¬Py,Pf(xy)],[¬Px,Qxg(x)],[¬Px,¬Pg(x),¬Rcg(x)]]');
    // },

    simplifyCNF: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula(
            '(p ∨ q) ∧ (q ∨ q ∨ r) ∧ (q ∨ r ∨ t) ∧ (r ∨ s) ∧ (s ∨ r) ∧ p '
        );
        var cnf = m.simplifyClauses(m.cnf(f));
        assertEqual(cnf, '[[p],[q,r],[r,s]]');
    },

    simplifyCNF2: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('((p∧(Fa∧Fb))∨(p∧(Fc∧Fd)))∧((q∧(Fe∧Ff))∨(q∧(Fg∧Fh)))');
        var cnf = m.simplifyClauses(m.cnf(f));
        assertEqual(cnf, '[[p],[q],[Fa,Fc],[Fa,Fd],[Fb,Fc],[Fb,Fd],[Fe,Fg],[Fe,Fh],[Ff,Fg],[Ff,Fh]]');
    },

    tseitin1: function() {
        var parser1 = new Parser();
        var parser2 = new Parser();
        var m1 = new ModelFinder([parser1.parseFormula('p')], parser1);
        var m2 = new ModelFinder([parser2.parseFormula('p')], parser2);
        var f = parser1.parseFormula('((p∨q)∧r)→¬s');
        // var tseitin = parser2.parseFormula('($↔¬s)∧($↔(p∨q))∧($2↔($∧r))∧($3↔($2→$3))∧$3');
        // [[$3],[$,¬p],[$,¬q],[$,¬$2],[r,¬$2],[$2,$3],[$3,s],[p,q,¬$],[$2,¬$,¬r],[¬$2,¬$3,¬s]]
        var res = m1.tseitinCNF(f);
        var tseitin = parser2.parseFormula('($↔(p∨q))∧($2↔($∧r))∧($3↔($2→¬s))∧$3');
        var cnf = m2.cnf(tseitin);
        // Compare as sets of clauses (clause order may differ between
        // tseitinCNF and cnf even though the clause contents match).
        var resSorted = res.map(function(c){return c.toString();}).sort().join('|');
        var cnfSorted = cnf.map(function(c){return c.toString();}).sort().join('|');
        assertEqual(resSorted, cnfSorted);
    },

    partialTseitin: function() {
        // For input 'A↔(A↔B) |= A↔B' we need to make sure the unused tseitin
        // variables $1 etc. from the premise aren't used to construct the
        // tseitin transform of the conclusion.
        var parser = new Parser();
        var f1 = parser.parseFormula('A↔(A↔B)').nnf();
        var f2 = parser.parseFormula('A↔B').negate().nnf();
        var mf = new ModelFinder([f1,f2], parser);
        // var tseitin = parser2.parseFormula('($↔¬s)∧($↔(p∨q))∧($2↔($∧r))∧($3↔($2→$3))∧$3');
        // [[$3],[$,¬p],[$,¬q],[$,¬$2],[r,¬$2],[$2,$3],[$3,s],[p,q,¬$],[$2,¬$,¬r],[¬$2,¬$3,¬s]]
        assertEqual(mf.clauses.toString(), '[[A,B],[B,¬A],[¬A,¬B]]');  // not: [[$],[B,¬A],[A,B]]
    },

    // tseitin2_fails_because_in_cnf: function() {
    //     var parser = new Parser();
    //     var m = new ModelFinder([parser.parseFormula('p')], parser);
    //     var f = parser.parseFormula('(¬(p∨¬q)∧r)→¬s');
    //     var res = m.tseitinCNF(f);
    //     assertEqual(res.toString(), '[(p2↔¬s),(p3↔¬q),(p4↔(p∨p3)),(p5↔¬p4),(p6↔(p5∧r)),(p7↔(p6→p2)),p7]');
    // },

    transformation1: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀x∃y(Fx∧∀zHxyz)')], parser);
        // skolem: Fx & Hxf(x)z
        // tseitin: p & (p<->(Fx & Hxf(x)z)
        // cnf: p & (~p v Fx) & (~p v Hxf(x)z)) & (p v ~Fx v ~Hxf(x)z) 
        //    = p & (~p v Fx) & (~p v Hxf(x)z))
        // assertEqual(mf.clauses.toString(), '[[$xz],[Fx,¬$xz],[Hxf(x)z,¬$xz]]');
        // but since we don't tseitin expand conjunctions, we should simply get
        // Fx & Hxf(x)z
        assertEqual(mf.clauses.toString(), '[[Fx],[Hxf(x)z]]');
    },

    transformation2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∃y∀x(Fy→Fx)').nnf();
        var mf = new ModelFinder([f], parser);
        // skolem: Fy & ~Ff(y)
        // assertEqual(mf.clauses.toString(), '[[$y],[Fy,¬$y],[¬$y,¬Ff(y)]]');
        assertEqual(mf.clauses.toString(), '[[Fy],[¬Ff(y)]]');
    },

    transformation3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇p');
        f = parser.translateFromModal(f).nnf();
        var mf = new ModelFinder([f], parser);
        //assertEqual(mf.initFormulas.toString(), '[(Rwu∧pu)]');
        // assertEqual(mf.clauses.toString(), '[[$],[Rwu,¬$],[pu,¬$]]');
        assertEqual(mf.clauses.toString(), '[[Rwu],[pu]]');
        assertEqual(parser.expressionType['u'], 'world constant');
    },

    several_inputformulas: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('r∧p'), parser.parseFormula('q∧(r∧p)')];
        var m = new ModelFinder(initflas, parser);
        // assertEqual(m.clauses.toString(), '[[$],[$2],[r,¬$],[p,¬$],[q,¬$2]]');
        assertEqual(m.clauses.toString(), '[[r],[p],[q]]');
        initflas.push(parser.parseFormula('Fa'))
        m = new ModelFinder(initflas, parser);
        // assertEqual(m.clauses.toString(), '[[$3],[$4],[Fa],[r,¬$3],[p,¬$3],[q,¬$4]]');
        assertEqual(m.clauses.toString(), '[[r],[p],[q],[Fa]]');
    },

    modelclauses_quantified1: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x(Fx∨Gx)')];
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        m.groundIncremental(Infinity);
        // Domain {0}: one ground clause [F0, G0]
        assertEqual(m.groundClauses.length, 1);
        m = new Model(mf, 2, 0);
        m.groundIncremental(Infinity);
        // Domain {0,1}: two ground clauses
        assertEqual(m.groundClauses.length, 2);
    },

    modelclauses_quantified2: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃yGxy')];
        // skolemized: Gxf(x)
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        m.groundIncremental(Infinity);
        // Domain {0}: one ground clause with predicate G
        assertEqual(m.groundClauses.length, 1);
        assertEqual(m.groundClauses[0].literals[0].predicate, 'G');
        m = new Model(mf, 2, 0);
        m.groundIncremental(Infinity);
        // Domain {0,1}: two ground clauses
        assertEqual(m.groundClauses.length, 2);
        assertEqual(mf.constants.toString(), '[]');
    },

    modelclauses_quantified3: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃y(Fx∧∀zHxyz)')];
        // skolemized: (Fx∧Hxf(x)z)
        // Non-tseitin CNF: [[Fx],[Hxf(x)z]]
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        m.groundIncremental(Infinity);
        // Domain {0}: F0 forced, H0f(0)0 forced => 0 unforced ground clauses remain
        // (unit clauses are propagated during grounding)
        assertEqual(m.initOk, true);
        assertEqual(m.cellIndex['F[0]'].value, true);
        m = new Model(mf, 2, 0);
        m.groundIncremental(Infinity);
        // Domain {0,1}: F0, F1 forced; H clauses with function terms
        assertEqual(m.initOk, true);
        assertEqual(m.cellIndex['F[0]'].value, true);
        assertEqual(m.cellIndex['F[1]'].value, true);
    },

    countermodel1: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬p')], parser);
        for (var i=0; i<10; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 10);
        assertEqual(mf.model.toString().trim(), 'p: false');
    },

    countermodel2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('¬q')], parser);
        for (var i=0; i<10; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 10);
        assertEqual(mf.model.toString().trim(), 'p: true\nq: false');
    },

    countermodel3: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a,b)')], parser);
        for (var i=0; i<20; i++) {
            if (mf.nextStep()) break;
        }
        assert(i < 20);
        assert(mf.model.toString().indexOf('f: { (0,0,0) }')>0);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Ff(a)∧¬Ff(f(a))').nnf();
        var mf = new ModelFinder([f], parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assert(mf.model.toString().indexOf('f: { (0,1), (1,0) }')>0);
        assert(mf.model.toString().indexOf('a: 0')>0);
        assert(mf.model.toString().indexOf('F: { 1 }')>0);
    },

    countermodel5: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀xFx')], parser);
        var m = mf.nextStep();
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel6: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('Fa ∧ ¬Fb')];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel7: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀x∃yRxy ∧ ¬∃xRxx').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('R: { (0,1), (1,0) }') > 0);
    },

    countermodel8a: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('(∃xFx→∃xGx)→∀x(Fx→Gx)').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<800; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<500);
        assertEqual(mf.model.domain.length, 2);
    },

    countermodel8: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∃y∀x(Fx→Gx) ↔ (∃xFx → ∃xGx)').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<500);
        assertEqual(mf.model.domain.length, 2);
    },

    countermodel9: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∃y∃z∀x((Fx→Gy)∧(Gz→Fx))→∀x∃y(Fy↔Gy)').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<500);
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('F: { 1 }') > 0);
        assert(mf.model.toString().indexOf('G: { 0 }') > 0);
    },

    countermodel10: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('p→p').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<10; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<5);
    },
     
    countermodel_shortestformulawith3individuals: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀y∃x(Ryx ∧ ¬Rxy)').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 3);
    },

    countermodel_shortestformulawith4individuals: function() { 
        var parser = new Parser();
        var fs = [parser.parseFormula('∀z∀y∃x(Rzx ∧ ¬Rxy)').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<10000; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<10000);
        assertEqual(mf.model.domain.length, 4);
    },
    
    iterateTermValues: function() {
        // If termValues aren't iterated properly a countermodel is found for this valid formula.
        var parser = new Parser();
        var fs = [parser.parseFormula('Na∧∀x(Nx→Nf(x))→Nf(f(f(f(f(a)))))').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<1000; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(i, 1000);
    },
    
    countermodel_modal1: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('◇p'), parser.parseFormula('¬p')];
        fs = fs.map(function(f){return parser.translateFromModal(f).nnf()});
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 2);
        assert(mf.model.toString().indexOf('@: w0') > 0);
        assert(mf.model.toString().indexOf('R: { (w0,w1) }') > 0);
        assert(mf.model.toString().indexOf('p: { w1 }') > 0);
    },

    countermodel_modal2: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('□p→p')];
        fs = fs.map(function(f){return parser.translateFromModal(f).nnf()});
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assert(mf.model.verifyModel());
    },

    countermodel_modal3: function() {
        var parser = new Parser();
        var fs = [parser.translateFromModal(parser.parseFormula('□p')).nnf(),
                  parser.parseAccessibilityFormula('∀v∃u(Rvu)')];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assert(mf.model.toString().indexOf('R: { (w0,w0) }') > 0);
        assert(mf.model.toString().indexOf('p: { w0 }') > 0);
    },

    countermodel_s5: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('□p')];
        fs = fs.map(function(f){
            var f2 = parser.translateFromModal(f).nnf();
            return parser.stripAccessibilityClauses(f2);
        });
        var mf = new ModelFinder(fs, parser, [], true);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assertEqual(mf.model.toString().indexOf('R:'), -1);
        assert(mf.model.toString().indexOf('p: { w0 }') >= 0);
    },

    totalfunctions1: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('f(a)=a∧¬Fb').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assert(mf.model.toString().indexOf('f: { (0,0) }') > 0);
    },

    totalfunctions2: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('f(a)=a∧(Fa∨¬Fa)∧g(a,b)=a').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.verifyModel());
    },

    github_issue_3_chrome: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(((∀x(Mx→(◇Px∧◇¬Px))∧∃xMx)∧(∀x(Sx→(◇Mx∧◇¬Mx))∧∃xSx))→(∀x(Sx→(◇Px∧◇¬Px))∧∃xSx))');
        fs = [parser.translateFromModal(f).negate().nnf(),
              parser.parseAccessibilityFormula('∀v∀uRvu'),
              parser.parseAccessibilityFormula('∀v∀u∀t(Rvu→(Rut→Rvt))'),
              parser.parseAccessibilityFormula('∀v∀u∀t(Rvu→(Rvt→Rut))')];
        var mf = new ModelFinder(fs, parser, [], true);
        for (var i=0; i<1000; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<1000);
        assertEqual(mf.model.worlds.length, 2);
    },

    two_worlds_one_individual: function() {
        var parser = new Parser();
        var f = parser.parseFormula('∀x(x=a) ∧ Fa → □Fa');
        fs = [parser.translateFromModal(f).negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<100);
        assertEqual(mf.model.worlds.length, 2);
    },

    numeric_constants_github26: function() {
        // github #26: numeric user constants like '0','1' must not be confused
        // with domain element numerals; the formula below is valid so no
        // countermodel should be found
        var parser = new Parser();
        var parsedInput = parser.parseInput('∀xc(x,1)=1,∀x(x=1↔¬x=0),∀xc(0,x)=1|=c(a,c(b,b))=1');
        var premises = parsedInput[0];
        var conclusion = parsedInput[1];
        var initFormulas = premises.concat([conclusion.negate()]).map(f => f.nnf());
        var mf = new ModelFinder(initFormulas, parser);
        for (var i=0; i<200; i++) {
            if (mf.nextStep()) {
                assert(false, 'should not find countermodel for valid formula');
                return;
            }
        }
        assert(true);
    },

    multidigit_atom_distinct: function() {
        // R(1,11) and R(11,1) must be treated as distinct atoms when
        // grounding symmetry-like clauses on domains with multi-digit
        // indices. 12*12 tuples minus 12 x=y tautologies leaves 132
        // ground clauses; any collision silently drops further clauses.
        var parser = new Parser();
        var f = parser.parseFormula('∀x∀y(Rxy→Ryx)').nnf();
        var mf = new ModelFinder([f], parser);
        var m = new Model(mf, 12, 0);
        m.groundIncremental(Infinity);
        assertEqual(m.groundClauses.length, 132);
    },

    modal_equality_dne7: function() {
        // ◇a=b∧¬¬¬¬a=c→b=c is valid; modelfinder must not find countermodel
        var parser = new Parser();
        var f = parser.parseFormula('◇a=b∧¬¬¬¬a=c→b=c').negate();
        var mfParser = parser.copy();
        var initFormulas = [mfParser.translateFromModal(f).nnf()];
        var mf = new ModelFinder(initFormulas, mfParser);
        for (var i=0; i<200; i++) {
            if (mf.nextStep()) {
                assert(false, 'should not find countermodel for valid formula');
                return;
            }
        }
        assert(true);
    },

    s5_skolem_world_args: function() {
        // □∃xFx→□∃xFx is a tautology; modelfinder must not find a countermodel.
        // This exercises a bug where skolem functions with world-variable
        // arguments (e.g. f(w) from skolemizing ∀w∃x...) only got cells for
        // the individual domain, not the world domain.
        var parser = new Parser();
        var f = parser.parseFormula('□∃xFx→□∃xFx');
        var mfParser = parser.copy();
        var initFormulas = [mfParser.translateFromModal(f).negate().nnf()];
        var accFlas = [mfParser.parseAccessibilityFormula('∀v∀uRvu').nnf()];
        var mf = new ModelFinder(initFormulas, mfParser, accFlas, true);
        for (var i=0; i<1000; i++) {
            if (mf.nextStep()) {
                assert(false, 'should not find countermodel for □∃xFx→□∃xFx');
                return;
            }
        }
        assert(true);
    },

    // tseitin_mixed_arg_types: function() {
    //     // Reported model: F={(1,w0)} on a single reflexive world was not
    //     // a countermodel (premise fails at x=1; also in a one-world
    //     // reflexive frame premise and conclusion are equivalent).
    //     // Root cause: tseitin predicates' argument order (world var first,
    //     // individual second) mismatched createCells' assumption that the
    //     // world arg is always last, so some ground clauses referenced
    //     // non-existent cells and were silently unsatisfied.
    //     var parser = new Parser();
    //     var input = '□∀x(Fx↔□∀y(Fy↔□∀z(Fz↔□Fx)))|=◇∀x(Fx↔□∀y(Fy↔□∀z(Fz↔□Fx)))';
    //     var parsed = parser.parseInput(input);
    //     var premises = parsed[0];
    //     var conclusion = parsed[1];
    //     var initFormulas = premises.concat([conclusion.negate()]);
    //     var mfParser = parser.copy();
    //     var mfFormulas = initFormulas.map(function(f) {
    //         return mfParser.translateFromModal(f).nnf();
    //     });
    //     var accFlas = [mfParser.parseAccessibilityFormula('∀vRvv').nnf()];
    //     var mf = new ModelFinder(mfFormulas, mfParser, accFlas, false);
    //     for (var i=0; i<5000; i++) {
    //         if (mf.nextStep()) {
    //             assert(mf.model.verifyModel(),
    //                    'returned model must satisfy all ground clauses');
    //             return;
    //         }
    //     }
    //     // Either no model in 5000 steps, or a verified one — both acceptable.
    //     assert(true);
    // },

    tseitin_fallback_predicates_kept: function() {
        // When plain CNF blows up (CNF_TOO_BIG), the plain list is
        // populated with tseitin clauses as a fallback, so the chosen
        // clause set may reference tseitin predicates even on the
        // "non-tseitin" branch. Those predicates must remain registered
        // in the parser; otherwise createCells skips them and nextStep
        // returns a model in which the $N auxiliaries are uninterpreted.
        var parser = new Parser();
        var input = '□(□(◇□P↔◇□Q)↔◇□R)↔□(□P↔(□Q↔□R))';
        var parsed = parser.parseInput(input);
        var premises = parsed[0];
        var conclusion = parsed[1];
        var initFormulas = premises.concat([conclusion.negate()]);
        var mfParser = parser.copy();
        var mfFormulas = initFormulas.map(function(f) {
            return mfParser.translateFromModal(f).nnf();
        });
        var accFlas = [
            mfParser.parseAccessibilityFormula('∀vRvv').nnf(),
            mfParser.parseAccessibilityFormula('∀v∀u(Rvu→Ruv)').nnf(),
            mfParser.parseAccessibilityFormula('∀v∀u∀t(Rvu→(Rut→Rvt))').nnf()
        ];
        var mf = new ModelFinder(mfFormulas, mfParser, accFlas, false);
        var ok = true;
        for (var c = 0; c < mf.clauses.length; c++) {
            for (var l = 0; l < mf.clauses[c].length; l++) {
                var lit = mf.clauses[c][l];
                var atom = lit.sub || lit;
                if (!mfParser.expressionType[atom.predicate]) {
                    assert(mfParser.expressionType[atom.predicate],
                       'predicate ' + atom.predicate + ' in clause must be registered in parser');
                    ok = false;
                }
            }
        }
        assert(ok, 'all predicates in clauses must be registered in parser');
    },

}
