<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>TGP testdrive</title>
<link href="https://fonts.googleapis.com/css?family=M+PLUS+1p:400,500&display=swap" rel="stylesheet">
<link rel="stylesheet" href="style.css" type="text/css">
<?php
$scripts = array("array", "formula", "parser", "prover", "equality", "modelfinder", "sentree", "painter");
if (isset($_GET['debug'])) {
    foreach ($scripts as $script) {
        print "<script type='text/javascript' src='$script.debug.js?".time()."'></script>\n";
    }
    ?>
    <script>
    function log(str) {
         if (!self.debugWin) debugPopup();
         debugWin.document.write("<pre>"+str+"</pre>");
    }
    function debugPopup() {
        self.debugWin = self.open("about:blank","debugWin");
        if (!self.debugWin) alert("unblock popups!");
    }
    log("hello, this is the debugging window");
    </script>
    <?php
}
else {
    $allscripts = implode("-", $scripts);
    print "<script type='text/javascript' src='$allscripts.js'></script>\n";
}
?>
</head>

<body id="testdrive" style="margin:10px 50px;">

<h2>Tree Proof Generator Test Drive</h2>

<h3>Valid Cases</h3>

<table style="max-width:1200px;">
    <tr><th>Label</th><th>Input</th><th>Time</th><th>Steps</th><th>Nodes</th></tr>
<?php
$valid_tests = [
   ['simp', '(p∨(q∧r))→((p∨q)∧(p∨r))'],
   ['merg', '¬((p∧¬(p→p))∨¬(p→p))'],
   ['fun', '∀ x F(x) → Ff(a)'],
   ['func', '¬(Pa∧¬Pf(f(a))∧∀x(Px→Pf(x)))'],
   ['bost2nnf', '¬(∀x(f(x)∧g(a)∨¬f(x)∧¬g(a)) ∧ ∀y∀z(f(b)∧¬g(y)∨g(z)∧¬f(b)) ∨ ∀w(f(d)∧¬g(w)∨¬f(d)∧g(w)) ∧ ∀s((¬f(s)∨g(e)) ∧ (¬g(k)∨f(s))))'],
   ['t5', '∃x(P∧Fx)↔P∧∃xFx'],
   ['t6', '∀x∃y(Fx↔Gy)→∃y∃z∀x((Fx→Gy)∧(Gz→Fx))'],
   ['t7', '∃y∃z∀x((Fx→Gy)∧(Gz→Fx))→∀x∃y(Fx↔Gy)'],
   ['t8', '∀x(Fx→Ff(x))∧Ff(a)→Ff(f(f(a)))'],
   ['t9', '∀x(Fx→Ff(x))∧Ff(g(f(a),b))→Ff(f(f(g(f(a),b))))'],
   ['ddelta', '¬∀x(Fx∧∃y¬Fy)'],
   ['b162.2', '∀y∃x(Fx∧Gy)→∃x∀y(Fx∧Gy)'],
   ['b164.1', '∃x(Fx→∀xFx)'],
   ['b164.k', '∀x∃y(Fx↔Gy)↔∃y∀x(Fx→Gy)∧∃y∀x(Gy→Fx)'],
   ['b164.l', '∀x∃y(Fx↔Gy)↔∃y∃z∀x((Fx→Gy)∧(Gz→Fx))'],
   ['conpos', '∀y(Iy→∀x(Px↔Cxy))∧∃yIy→∀x(Px↔∀y(Iy→Cxy))'],
   ['carnap', '(∃xFx→Fw)∧(¬∃xFx∧∃xGx→Gw)↔(∃x(Fx∨(¬∃yFy∧Gx))→(Fw∨(¬∃yFy∧Gw)))'],
   ['fd1eaff', 'Ac, ∀x(Ax→Tx), ∀x(Mx→¬Tx), Mb, ∀xIxx, ∀x∀y(Ixy→Iyx), ∀x∀y(Ixy→(Ax→Ay)), ∀x∀y(Ixy→(Mx→My)), ∀x∀y(Ixy→(Tx→Ty)) |= ¬Ibc'],
   ['id1', 'c=b ∧ Fc → Fb'],
   ['id2', 'a=b ∧ b=c ∧ Paa → Pcc'],
   ['id3', '∀x∀y(f(x)=f(y)→x=y), f(a)=k, f(b)=k |= a=b'],
   ['id4', '∀x∀y(f(x)=f(y)→x=y), ∀x∃y(Ryx∧f(y)=k) |= ∃y∀xRyx'],
   ['beckert97a', '∀x(g(x)=f(x) ∨ ¬(x=a)) ∧ ∀x(g(f(x))=x) ∧ b=c ∧ Pg(g(a))b → Pac'],
   ['beckert98ex4', '∀x(g(x)=f(x) ∨ ¬(x=a)) ∧ ∀x(f(x)=x) ∧ Pg(a)f(b) → Pab'],
   ['dv98ex1.1', '∃x∃y∃u∃v((a = b → g(x, u, v) = g(y, f(c), f(d))) ∧ (c = d → g(u, x, y) = g(v, f(a), f(b))))'],
   ['franssen08fibo', '∀xp(x, z) = x ∧ ∀x∀yp(x,y) = p(y,x) ∧ f(z) = z ∧ f(s(z)) = s(z) ∧ ∀yf(s(s(y))) = p(f(y), f(s(y))) → f(s(s(z))) = s(z)'],
   ['multiinst', '(∀x(P(x)→P(f(x)))) ∧ P(d)→P(f(f(f(d))))'],
   ['tseitin', '((∃x∀y(Px↔Py)↔(∃zQz↔∀wQw))↔(∃x2∀x3(Qx2↔Qx3)↔(∃x4Px4↔∀x5Px5)))'],
   ['pel1', '((p→q)↔(¬q→¬p))'],
   ['pel2', '(¬¬p↔p)'],
   ['pel3', '(¬(p→q)→(q→p))'],
   ['pel4', '((¬p→q)↔(¬q→p))'],
   ['pel5', '(((p∨q)→(p∨r))→(p∨(q→r)))'],
   ['pel6', '(p∨¬p)'],
   ['pel7', '(p∨¬(¬(¬p)))'],
   ['pel8', '(((p→q)→p)→p)'],
   ['pel9', '((((p∨q)∧(¬p∨q))∧(p∨¬q)) → ¬(¬p∨¬q))'],
   ['pel10', '¬(¬(p↔q)∧(q→r) ∧(r→(p∧q))∧(p→(q∨r)))'],
   ['pel11', '(p↔p)'],
   ['pel12', '(((p↔q)↔r) ↔ (p↔(q↔r)))'],
   ['pel13', '((p∨(q∧r))↔((p∨q)∧(p∨r)))'],
   ['pel14', '((p↔q)↔((q∨¬p)∧(¬q∨p)))'],
   ['pel15', '((p→q)↔(¬p∨q))'],
   ['pel16', '((p→q)∨(q→p))'],
   ['pel17', '(((p∧(q→r))→s) ↔ (((¬p∨q)∨s)∧((¬p∨¬r)∨s)))'],
   ['pel18', '∃y∀x(Fy→Fx)'],
   ['pel19', '∃x∀y∀z((Py→Qz)→(Px→Qx))'],
   ['pel20', '(∀x∀y∃z∀w((Px∧Qy)→(Rz∧Sw)) → ∃x1∃y1((Px1∧Qy1)→∃z1(Rz1)))'],
   ['pel21', '¬(¬∃x(P↔Fx) ∧∃x1(P→Fx1)∧∃x2(Fx2→P))'],
   ['pel22', '∀x(P↔Fx)→(P↔∀yFy)'],
   ['pel23', '∀x(P∨Fx)↔(P∨∀yFy)'],
   ['pel24', '¬(¬∃x(Px∧Rx) ∧ ¬∃y(Sy∧Qy) ∧ ∀v(Pv→(Qv∨Rv)) ∧ (¬∃yPy→∃zQz) ∧ ∀w((Qw∨Rw)→Sw))'],
   ['pel25', '¬(¬∃x(Qx∧Px) ∧ ∃yPy ∧ ∀y(Fy→(¬Gy∧Ry)) ∧ ∀y(Py→(Gy∧Fy)) ∧ (∀y(Py→Qy)∨∃z(Pz∧Rz)))'],
   ['pel26', '¬(¬(∀x(Px→Rx)↔∀y(Qy→Sy)) ∧ (∃zPz↔∃zQz) ∧ ∀x∀y((Px∧Qy)→(Rx↔Sy)))'],
   ['pel26nnf', '¬(((q(a)∧ ¬s(a))∧ ∀x(¬p(x)∨r(x))∨ (p(b)∧ ¬r(b))∧ ∀y(¬q(y)∨s(y)))∧ (p(c)∧ q(d)∨∀z¬p(z)∧ ∀w¬q(w))∧ ∀v∀w((¬p(v)∨¬q(w))∨r(v)∧ s(w)∨¬r(v)∧ ¬s(w)))'],
   ['pel27', '¬(¬∀x (J(x) → ¬I(x)) ∧ ∃y (F(y) ∧ ¬G(y)) ∧ ∀z (F(z) → H(z)) ∧ ∀w ((J(w) ∧ I(w)) → F(w)) ∧ (∃x2 (H(x2) ∧ ¬G(x2)) → ∀x3 (I(x3) → ¬H(x3))))'],
   ['pel28', '¬(¬∀x ((P(x) ∧ F(x)) → G(x)) ∧ ∀y (P(y) → ∀z (Q(z))) ∧ (∀w (Q(w) ∨ R(w)) → ∃x2 (Q(x2) ∧ S(x2))) ∧ (∃x3 (S(x3)) → ∀x4 (F(x4) → G(x4))))'],
   ['pel29', '¬(¬((∀x (F(x) → H(x)) ∧ ∀y (G(y) → J(y))) ↔ ∀z ∀w ((F(z) ∧ G(w)) → (H(z) ∧ J(w)))) ∧ (∃x2 (F(x2)) ∧ ∃x3 (G(x3))))'],
   ['pel30', '¬(¬∀x (I(x)) ∧ ∀y ((F(y) ∨ G(y)) → ¬H(y)) ∧ ∀z ((G(z) → ¬I(z)) → (F(z) ∧ H(z))))'],
   ['pel31', '¬(¬∃x (I(x) ∧ J(x)) ∧ ¬∃y (F(y) ∧ (G(y) ∨ H(y))) ∧ ∃z (I(z) ∧ F(z)) ∧ ∀w (¬H(w) → J(w)))'],
   ['pel32', '¬(¬∀x ((F(x) ∧ K(x)) → J(x)) ∧ ∀y ((F(y) ∧ (G(y) ∨ H(y))) → I(y)) ∧ ∀z ((I(z) ∧ H(z)) → J(z)) ∧ ∀w (K(w) → H(w)))'],
   ['pel33', '∀x ((P(a) ∧ (P(x) → P(b))) → P(c)) ↔ ∀y ((¬P(a) ∨ (P(y) ∨ P(c))) ∧ (¬P(a) ∨ (¬P(b) ∨ P(c))))'],
   ['pel34', '(∃x ∀y (P(x) ↔ P(y)) ↔ (∃z (Q(z)) ↔ ∀w (Q(w)))) ↔ (∃x2 ∀x3 (Q(x2) ↔ Q(x3)) ↔ (∃x4 (P(x4)) ↔ ∀x5 (P(x5))))'],
   ['pel35', '∃x ∃y (P(x,y) → ∀z ∀w (P(z,w)))'],
   ['pel36', '¬(¬∀x ∃y (H(x,y)) ∧ ∀z ∃w (F(z,w)) ∧ ∀x2 ∃x3 (G(x2,x3)) ∧ ∀x4 ∀x5 ((F(x4,x5) ∨ G(x4,x5)) → ∀x6 ((F(x5,x6) ∨ G(x5,x6)) → H(x4,x6))))'],
   ['pel37', '¬(¬∀x ∃y (R(x,y)) ∧ ∀z ∃w ∀x2 ∃x3 (P(x2,z) → ((P(x3,w) ∧ P(x3,z)) ∧ (P(x3,w) → ∃x4 (Q(x4,w))))) ∧ ∀x5 ∀x6 (¬P(x5,x6) →∃x7 (Q(x7,x6))) ∧ (∃x8 ∃x9 (Q(x8,x9)) → ∀y1 (R(y1,y1))))'],
   ['pel38', '∀x ((P(a) ∧ (P(x) → ∃y (P(y) ∧ R(x,y)))) → ∃z ∃w ((P(z) ∧ R(x,w)) ∧ R(w,z))) ↔ ∀x2 ((((¬P(a)) ∨ P(x2)) ∨ ∃x3 ∃x4 ((P(x3) ∧ R(x2,x4)) ∧ R(x4,x3))) ∧ (((¬P(a)) ∨ (¬∃x5 (P(x5) ∧ R(x2,x5)))) ∨ ∃x6 ∃x7 ((P(x6) ∧ R(x2,x7)) ∧ R(x7,x6))))'],
   ['pel39', '¬∃x ∀y (F(y,x) ↔ ¬F(y,y))'],
   ['pel40', '∃x ∀y (F(y,x) ↔ F(y,y)) → ¬∀z ∃w ∀x2 (F(x2,w) ↔ ¬F(x2,z))'],
   ['pel43', '∀x∀y(Qxy ↔ ∀z(Fzx ↔ Fzy)) |= ∀x∀y(Qxy ↔ Qyx)'],
   ['pel48', '(a=b ∨ c=d) ∧ (a=c ∨ b=d) → (a=d ∨ b=c)'],
   ['pel49', '∃x∃y∀z(z=x ∨ z=y) ∧ Pa ∧ Pb ∧ ¬(a=b) → ∀xPx'],
   ['pel51', '∃z∃w∀x∀y(Fxy ↔ (x=z ∧ y=w)) |= ∃z∀x(∃w∀y(Fxy ↔ y=w) ↔ x=z)'],
   ['pel52', '∃z∃w∀x∀y(Fxy ↔ (x=z ∧ y=w)) |= ∃w∀y(∃z∀x(Fxy ↔ x=z) ↔ y=w)'],
   ['pel55', '∃x(Lx ∧ Kxa), La ∧ Lb ∧ Lc, ∀x∀y(Kxy → Hxy), ∀x∀y(Kxy → ¬ Rxy), ∀x (Hax → ¬ Hcx), ∀x(¬x=b → Hax), ∀x(¬ Rxa → Hbx), ∀x(Hax → Hbx), ∀x(Lx → (x=a ∨ x=b ∨ x=c)),  ∀x∃y(¬Hxy), ¬(a=b) |= Kaa'],
   ['pel56', '∀x(∃y(Fy ∧ x=f(y)) →Fx) ↔ ∀x(Fx →  Ff(x))'],
   ['pel57', 'Ff(a,b)f(b,c), Ff(b,c)f(a,c), ∀x∀y∀z(Fxy ∧ Fyz → Fxz) |= Ff(a,b)f(a,c)'],
   ['pel58', '∀x∀yf(x)=g(y) |= ∀x∀yf(f(x))=f(g(y))'],
   ['pel59', '∀x(P(x) ↔ ¬P(f(x))) → ∃x(P(x) ∧ ¬P(f(x)))'],
   ['pel61', '∀x∀y∀zf(x,f(y,z))=f(f(x,y),z) |= ∀x∀y∀z∀wf(x,f(y,f(z,w)))=f(f(f(x,y),z),w)'],
   ['rel1', '(∀x∃yCxy∧∀x∀y(Cxy→Cyx)∧∀x∀y∀z((Cxy∧Cyz)→Cxz)) → ∀xCxx'],
   ['mod1', '(□p ∧ ◇q)→◇(p∧q)'],
   ['mod2', '◇(p ∨ q)↔(◇p ∨ ◇q)'],
   ['s5', 'p→◇p||universality'],
   ['narrow_D', '(p→□r)→((p∧q)→□r)||seriality'],
   ['04vsG0_S4', '((A ∧ ¬□A)→□¬□A) ∧ ((¬A ∧ ◇A) →□◇A) → (◇□A→□◇A)||reflexivity|transitivity'],
   ['pel54', '∀y∃z∀x(Fxz ↔ x=y) |= ¬∃w∀x(Fxw ↔ ∀u(Fxu → ∃y(Fyu ∧ ¬∃z(Fzu ∧ Fzy))))'],
   ['beckert97bid','∀x(i(u,x)=x) ∧ ∀x∀y∀z(i(i(x,y),i(i(y,z),i(x,z)))=u) ∧ ∀x∀y(i(i(x,y),y) = i(i(y,x),x)) → ∀x∀y∀z∃w(i(x,w)=u ∧ w=i(y,i(z,y)))']
];

foreach ($valid_tests as $test) {
    print("<tr><td><a href='./#$test[1]'>$test[0]</a> (<a href='./?debug=1#$test[1]'>d</a>)</td><td class='formula valid'>$test[1]</td><td></td><td></td><td></td></tr>\n");
}
?>
</table>

<h3>Invalid Cases</h3>

<table>
    <tr><th>Label</th><th>Input</th><th>Time</th><th>Steps</th><th>Nodes</th></tr>
<?php
$invalid_tests = [
    ['i1', 'p'],
    ['i2', '((p→q)↔(q→p))'],
    ['i3', '∀xFx'],
    ['i4', '∃xFx'],
    ['i5', '∀x∃yRxy'],
    ['i6', '∃y∀xFxy'],
    ['ifun', '∀x∃y (Fx → Ff(y)) → (¬Fa ∨ Ff(a))'],
    ['Her', '¬∀x((Fx ∧ ¬Fa)∨ Ga)'],
    ['bost1', '∀x∀y∀z(Fxy∧Fyz→Fxz) ∧ ∀x∀y(Fxy→Fyx) ∧ ∃x∃yFxy → ∀xFxx'],
    ['2ind', '¬∃x∃y(Fx∧¬Fy)'],
    ['3ind', '¬∀y∃x(Ryx ∧ ¬Rxy)'],
    ['4indsimp', '¬(Fa ∧ Ga ∧ Fb ∧ ¬Gb ∧ ¬Fc ∧ Gc ∧ ¬Fd ∧ ¬Gd)'],
    ['4ind', '∀z∀y∃x(Rzx ∧ ¬Rxy)'],
    ['bx', '∀y∃xFxy→∃x∀yFxy'],
    ['bn', '∃y∃z∀x((Fx→Gy)∧(Gz→Fx))→∀x∃y(Fy↔Gy)'],
    ['conpos1', '∀y(Iy→∀x(Px↔Cxy))→∀x(Px↔∀y(Iy→Cxy))'],
    ['conpos2', '∀x(Px↔∀y(Iy→Cxy))→∀y(Iy→∀x(Px↔Cxy))'],
    ['pel48s', '(a=b ∨ c=d) ∧ (a=c ∨ b=d) → a=d'],
    ['T_in_K', 'p→◇p'],
    ['emil_in_K4', '◇□A → (◇□B → ◇□(A ∧ B))||transitivity'],
    ['T_in_K', 'p→◇p'],
    ['parsercopy', 'p → ◇□p↔□◇□p'],
    ['04vsG0_K4', '((A ∧ ¬□A)→□¬□A) ∧ ((¬A ∧ ◇A) →□◇A) → (◇□A→□◇A)||transitivity'],
    ['redinexD', '◇(p→□◇p)||seriality'],
    ['boxreds4', '◇□p↔□◇□p||reflexivity|transitivity'],
    ['github16', '((∃x(◇(Ox∧Px)∧□(Ox→Mx)))∧(∀x(◇(Ox∧Mx)→□(Ox→Sx))∧◇∃x(Ox∧Mx)))→(∃x((Ox∧Sx)∧◇(Ox∧Px)))'],
    ['7ind', '¬∀z∀y∃x¬((Rxy → Ryx) ∨ Rzx)'],
    ['infinity', '¬(∀x∃yFxy ∧ ∀x∀y∀z(Fxy∧Fyz→Fxz) ∧ ∀x¬Fxx)'],
];
// $invalid_tests = [];

foreach ($invalid_tests as $test) {
    print("<tr><td><a href='./#$test[1]'>$test[0]</a> (<a href='./?debug=1#$test[1]'>d</a>)</td><td class='formula invalid'>$test[1]</td><td></td><td></td><td></td></tr>\n");
}
?>
</table>

    
<script type="text/javascript">

var tests = [];
document.querySelectorAll('.formula').forEach(function(td) {
    var formula = td.innerHTML;
    td.onclick = function(e) {
        prove(td.innerHTML, td.parentNode, td.className.indexOf('invalid')==-1);
    }
    tests.push(td.onclick);
});

var prover;
var stopTimer;
var provingAll;
function prove(fla, tableRow, isValid) {
    var parser = new Parser();
    var accessibilityConstraints = null;
    if (fla.indexOf('||') > 0) {
        accessibilityConstraints = fla.split('||')[1].split('|');
        fla = fla.split('||')[0];
    }
    console.log('testing '+fla);
    var parsedInput = parser.parseInput(fla);
    var premises = parsedInput[0];
    var conclusion = parsedInput[1];
    var initFormulas = premises.concat([conclusion.negate()]);
    var startTime = performance.now();
    prover = new Prover(initFormulas, parser, accessibilityConstraints);
    prover.onfinished = function(status) {
        var endTime = performance.now();
        console.log('done with '+fla);
        var calcTime = Math.round(endTime - startTime);
        var timeTd = tableRow.childNodes[2];
        var stepsTd = tableRow.childNodes[3];
        var nodesTd = tableRow.childNodes[4];
        if (status != isValid) {
            timeTd.innerHTML = "<b>wrongly found "+(status ? "valid" : "invalid")+"!</b>";
        }
        else {
            timeTd.innerHTML = calcTime;
            stepsTd.innerHTML = prover.step;
        }
        if (status) {
            nodesTd.innerHTML = new SenTree(prover.tree, parser).nodes.length;
        }
        if (provingAll) {
            // console.log('clearing timer '+stopTimer);
            clearTimeout(stopTimer);
            setTimeout('proveNext()', 100);
        }
    };
    prover.start();
}

var index;
var timeLimit;
function proveAll(tLimit) {
    index = 0;
    provingAll = true;
    timeLimit = tLimit;
    proveNext();
}

function proveNext() {
    if (index >= tests.length) {
        provingAll = false;
        return;
    }
    console.log('launching test '+self.index);
    stopTimer = setTimeout(function() {
        console.log('aborting test');
        prover.stop();
        proveNext();
    }, timeLimit);
    tests[index]();
    index++;
}

</script>

<br><br><br><br>

<div style="position:fixed; bottom:0; left:0; padding:10px; width:100%; background-color:#ccc">
<form action="#" method="get" style="display:inline">
<input type="button" onclick="proveAll(this.form.l.value)" value="run all tests"> 
Limit <input type="text" size="7" name="l" value="5000"> ms/test
</form>
</div>

</body>
</html>
