<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>TGP testdrive</title>
<link href="https://fonts.googleapis.com/css?family=M+PLUS+1p:400,500&display=swap" rel="stylesheet">
<link rel="stylesheet" href="style.css" type="text/css">

<?php
$scripts = array("array", "formula", "parser", "prover", "modelfinder", "sentree", "painter");
$allscripts = implode("-", $scripts);
print "<script type='text/javascript' src='$allscripts.js'></script>\n";
?>

</head>

<body id="testdrive">

<h2>Tree Proof Generator Test Drive</h2>

<h3>Valid Formulas</h3>

<table>

<tr><td>simp</td><td class="formula">(p∨(q∧r))→((p∨q)∧(p∨r))</td><td></td></tr>

<tr><td>merg</td><td class="formula">¬((p∧¬(p→p))∨¬(p→p))</td><td></td></tr>

<tr><td>fun</td><td class="formula">∀ x F(x) → Ff(a)</td><td></td></tr>

<tr><td>func</td><td class="formula">¬(Pa∧¬Pf(f(a))∧∀x(Px→Pf(x)))</td><td></td></tr>

<tr><td>bost2nnf</td><td class="formula">¬(∀x(f(x)∧g(a)∨¬f(x)∧¬g(a)) ∧ ∀y∀z(f(b)∧¬g(y)∨g(z)∧¬f(b)) ∨ ∀w(f(d)∧¬g(w)∨¬f(d)∧g(w)) ∧ ∀s((¬f(s)∨g(e)) ∧ (¬g(k)∨f(s))))</td><td></td></tr>

<tr><td>t5</td><td class="formula">∃x(P∧Fx)↔P∧∃xFx</td><td></td></tr>

<tr><td>t6</td><td class="formula">∀x∃y(Fx↔Gy)→∃y∃z∀x((Fx→Gy)∧(Gz→Fx))</td><td></td></tr>

<tr><td>t7</td><td class="formula">∃y∃z∀x((Fx→Gy)∧(Gz→Fx))→∀x∃y(Fx↔Gy)</td><td></td></tr>

<tr><td>t8</td><td class="formula">∀x(Fx→Ff(x))∧Ff(a)→Ff(f(f(a)))</td><td></td></tr>

<tr><td>t9</td><td class="formula">∀x(Fx→Ff(x))∧Ff(g(f(a),b))→Ff(f(f(g(f(a),b))))</td><td></td></tr>

<tr><td>ddelta</td><td class="formula">¬∀x(Fx∧∃y¬Fy)</td><td></td></tr>

<tr><td>b162.2</td><td class="formula">∀y∃x(Fx∧Gy)→∃x∀y(Fx∧Gy)</td><td></td></tr>

<tr><td>b164.1</td><td class="formula">∃x(Fx→∀xFx)</td><td></td></tr>

<tr><td>b164.k</td><td class="formula">∀x∃y(Fx↔Gy)↔∃y∀x(Fx→Gy)∧∃y∀x(Gy→Fx)</td><td></td></tr>

<tr><td>b164.l</td><td class="formula">∀x∃y(Fx↔Gy)↔∃y∃z∀x((Fx→Gy)∧(Gz→Fx))</td><td></td></tr>

<tr><td>conpos</td><td class="formula">∀y(Iy→∀x(Px↔Cxy))∧∃yIy→∀x(Px↔∀y(Iy→Cxy))</td><td></td></tr>

<tr><td>carnap</td><td class="formula">(∃xFx→Fw)∧(¬∃xFx∧∃xGx→Gw)↔(∃x(Fx∨(¬∃yFy∧Gx))→(Fw∨(¬∃yFy∧Gw)))</td><td></td></tr>

<tr><td>pel1</td><td class="formula">((p→q)↔(¬q→¬p))</td><td></td></tr>

<tr><td>pel2</td><td class="formula">(¬¬p↔p)</td><td></td></tr>

<tr><td>pel3</td><td class="formula">(¬(p→q)→(q→p))</td><td></td></tr>

<tr><td>pel4</td><td class="formula">((¬p→q)↔(¬q→p))</td><td></td></tr>

<tr><td>pel5</td><td class="formula">(((p∨q)→(p∨r))→(p∨(q→r)))</td><td></td></tr>

<tr><td>pel6</td><td class="formula">(p∨¬p)</td><td></td></tr>

<tr><td>pel7</td><td class="formula">(p∨¬(¬(¬p)))</td><td></td></tr>

<tr><td>pel8</td><td class="formula">(((p→q)→p)→p)</td><td></td></tr>

<tr><td>pel9</td><td class="formula">((((p∨q)∧(¬p∨q))∧(p∨¬q)) → ¬(¬p∨¬q))</td><td></td></tr>

<tr><td>pel10</td><td class="formula">¬(¬(p↔q)∧(q→r) ∧(r→(p∧q))∧(p→(q∨r)))</td><td></td></tr>

<tr><td>pel11</td><td class="formula">(p↔p)</td><td></td></tr>

<tr><td>pel12</td><td class="formula">(((p↔q)↔r) ↔ (p↔(q↔r)))</td><td></td></tr>

<tr><td>pel13</td><td class="formula">((p∨(q∧r))↔((p∨q)∧(p∨r)))</td><td></td></tr>

<tr><td>pel14</td><td class="formula">((p↔q)↔((q∨¬p)∧(¬q∨p)))</td><td></td></tr>

<tr><td>pel15</td><td class="formula">((p→q)↔(¬p∨q))</td><td></td></tr>

<tr><td>pel16</td><td class="formula">((p→q)∨(q→p))</td><td></td></tr>

<tr><td>pel17</td><td class="formula">(((p∧(q→r))→s) ↔ (((¬p∨q)∨s)∧((¬p∨¬r)∨s)))</td><td></td></tr>

<tr><td>pel18</td><td class="formula">∃y∀x(Fy→Fx)</td><td></td></tr>

<tr><td>pel19</td><td class="formula">∃x∀y∀z((Py→Qz)→(Px→Qx))</td><td></td></tr>

<tr><td>pel20</td><td class="formula">(∀x∀y∃z∀w((Px∧Qy)→(Rz∧Sw)) → ∃x1∃y1((Px1∧Qy1)→∃z1(Rz1)))</td><td></td></tr>

<tr><td>pel21</td><td class="formula">¬(¬∃x(P↔Fx) ∧∃x1(P→Fx1)∧∃x2(Fx2→P))</td><td></td></tr>

<tr><td>pel22</td><td class="formula">∀x(P↔Fx)→(P↔∀yFy)</td><td></td></tr>

<tr><td>pel23</td><td class="formula">∀x(P∨Fx)↔(P∨∀yFy)</td><td></td></tr>

<tr><td>pel24</td><td class="formula">¬(¬∃x(Px∧Rx) ∧ ¬∃y(Sy∧Qy) ∧ ∀v(Pv→(Qv∨Rv)) ∧ (¬∃yPy→∃zQz) ∧ ∀w((Qw∨Rw)→Sw))</td><td></td></tr>

<tr><td>pel25</td><td class="formula">¬(¬∃x(Qx∧Px) ∧ ∃yPy ∧ ∀y(Fy→(¬Gy∧Ry)) ∧ ∀y(Py→(Gy∧Fy)) ∧ (∀y(Py→Qy)∨∃z(Pz∧Rz)))</td><td></td></tr>

<tr><td>pel26</td><td class="formula">¬(¬(∀x(Px→Rx)↔∀y(Qy→Sy)) ∧ (∃zPz↔∃zQz) ∧ ∀x∀y((Px∧Qy)→(Rx↔Sy)))</td><td></td></tr>

<!--tr><td>pel26nnf</td><td class="formula">¬(((q(a)∧ ¬s(a))∧ ∀x(¬p(x)∨r(x))∨ (p(b)∧ ¬r(b))∧ ∀y(¬q(y)∨s(y)))∧ (p(c)∧ q(d)∨∀z¬p(z)∧ ∀w¬q(w))∧ ∀v∀w((¬p(v)∨¬q(w))∨r(v)∧ s(w)∨¬r(v)∧ ¬s(w)))</td><td></td></tr-->

<tr><td>pel27</td><td class="formula">¬(¬∀x (J(x) → ¬I(x)) ∧ ∃y (F(y) ∧ ¬G(y)) ∧ ∀z (F(z) → H(z)) ∧ ∀w ((J(w) ∧ I(w)) → F(w)) ∧ (∃x2 (H(x2) ∧ ¬G(x2)) → ∀x3 (I(x3) → ¬H(x3))))</td><td></td></tr>

<tr><td>pel28</td><td class="formula">¬(¬∀x ((P(x) ∧ F(x)) → G(x)) ∧ ∀y (P(y) → ∀z (Q(z))) ∧ (∀w (Q(w) ∨ R(w)) → ∃x2 (Q(x2) ∧ S(x2))) ∧ (∃x3 (S(x3)) → ∀x4 (F(x4) → G(x4))))</td><td></td></tr>

<tr><td>pel29</td><td class="formula">¬(¬((∀x (F(x) → H(x)) ∧ ∀y (G(y) → J(y))) ↔ ∀z ∀w ((F(z) ∧ G(w)) → (H(z) ∧ J(w)))) ∧ (∃x2 (F(x2)) ∧ ∃x3 (G(x3))))</td><td></td></tr>

<tr><td>pel30</td><td class="formula">¬(¬∀x (I(x)) ∧ ∀y ((F(y) ∨ G(y)) → ¬H(y)) ∧ ∀z ((G(z) → ¬I(z)) → (F(z) ∧ H(z))))</td><td></td></tr>

<tr><td>pel31</td><td class="formula">¬(¬∃x (I(x) ∧ J(x)) ∧ ¬∃y (F(y) ∧ (G(y) ∨ H(y))) ∧ ∃z (I(z) ∧ F(z)) ∧ ∀w (¬H(w) → J(w)))</td><td></td></tr>

<tr><td>pel32</td><td class="formula">¬(¬∀x ((F(x) ∧ K(x)) → J(x)) ∧ ∀y ((F(y) ∧ (G(y) ∨ H(y))) → I(y)) ∧ ∀z ((I(z) ∧ H(z)) → J(z)) ∧ ∀w (K(w) → H(w)))</td><td></td></tr>

<tr><td>pel33</td><td class="formula">∀x ((P(a) ∧ (P(x) → P(b))) → P(c)) ↔ ∀y ((¬P(a) ∨ (P(y) ∨ P(c))) ∧ (¬P(a) ∨ (¬P(b) ∨ P(c))))</td><td></td></tr>

<tr><td>pel34</td><td class="formula">(∃x ∀y (P(x) ↔ P(y)) ↔ (∃z (Q(z)) ↔ ∀w (Q(w)))) ↔ (∃x2 ∀x3 (Q(x2) ↔ Q(x3)) ↔ (∃x4 (P(x4)) ↔ ∀x5 (P(x5))))</td><td></td></tr>

<tr><td>pel35</td><td class="formula">∃x ∃y (P(x,y) → ∀z ∀w (P(z,w)))</td><td></td></tr>

<tr><td>pel36</td><td class="formula">¬(¬∀x ∃y (H(x,y)) ∧ ∀z ∃w (F(z,w)) ∧ ∀x2 ∃x3 (G(x2,x3)) ∧ ∀x4 ∀x5 ((F(x4,x5) ∨ G(x4,x5)) → ∀x6 ((F(x5,x6) ∨ G(x5,x6)) → H(x4,x6))))</td><td></td></tr>

<tr><td>pel37</td><td class="formula">¬(¬∀x ∃y (R(x,y)) ∧ ∀z ∃w ∀x2 ∃x3 (P(x2,z) → ((P(x3,w) ∧ P(x3,z)) ∧ (P(x3,w) → ∃x4 (Q(x4,w))))) ∧ ∀x5 ∀x6 (¬P(x5,x6) →∃x7 (Q(x7,x6))) ∧ (∃x8 ∃x9 (Q(x8,x9)) → ∀y1 (R(y1,y1))))</td><td></td></tr>

<tr><td>pel38</td><td class="formula">∀x ((P(a) ∧ (P(x) → ∃y (P(y) ∧ R(x,y)))) → ∃z ∃w ((P(z) ∧ R(x,w)) ∧ R(w,z))) ↔ ∀x2 ((((¬P(a)) ∨ P(x2)) ∨ ∃x3 ∃x4 ((P(x3) ∧ R(x2,x4)) ∧ R(x4,x3))) ∧ (((¬P(a)) ∨ (¬∃x5 (P(x5) ∧ R(x2,x5)))) ∨ ∃x6 ∃x7 ((P(x6) ∧ R(x2,x7)) ∧ R(x7,x6))))</td><td></td></tr>

<tr><td>pel39</td><td class="formula">¬∃x ∀y (F(y,x) ↔ ¬F(y,y))</td><td></td></tr>

<tr><td>pel40</td><td class="formula">∃x ∀y (F(y,x) ↔ F(y,y)) → ¬∀z ∃w ∀x2 (F(x2,w) ↔ ¬F(x2,z))</td><td></td></tr>

<tr><td>mod1</td><td class="formula">(□p ∧ ◇q)→◇(p∧q)</td><td></td></tr>

<tr><td>mod2</td><td class="formula">◇(p ∨ q)↔(◇p ∨ ◇q)</td><td></td></tr>
    
    
</table>

    <h3>Invalid Formulas</h3>
    
<table>
    
<tr><td>i1</td><td class="formula">p</td><td></td></tr>

<tr><td>i2</td><td class="formula">((p→q)↔(q→p))</td><td></td></tr>

<tr><td>i3</td><td class="formula">∀xFx</td><td></td></tr>

<tr><td>i4</td><td class="formula">∃xFx</td><td></td></tr>

<tr><td>i5</td><td class="formula">∀x∃yRxy</td><td></td></tr>

<tr><td>i6</td><td class="formula">∃y∀xFxy</td><td></td></tr>

<tr><td>ifun</td><td class="formula">∀x∃y (Fx → Ff(y)) → (¬Fa ∨ Ff(a))</td><td></td></tr>

<tr><td>Her</td><td class="formula">¬∀x((Fx ∧ ¬Fa)∨ Ga)</td><td></td></tr>

<tr><td>bost1</td><td class="formula">∀x∀y∀z(Fxy∧Fyz→Fxz) ∧ ∀x∀y(Fxy→Fyx) ∧ ∃x∃yFxy → ∀xFxx</td><td></td></tr>

<tr><td>2ind</td><td class="formula">¬∃x∃y(Fx∧¬Fy)</td><td></td></tr>

<tr><td>4ind</td><td class="formula">¬(Fa ∧ Ga ∧ Fb ∧ ¬Gb ∧ ¬Fc ∧ Gc ∧ ¬Fd ∧ ¬Gd)</td><td></td></tr>

<tr><td>bx</td><td class="formula">∀y∃xFxy→∃x∀yFxy</td><td></td></tr>

<tr><td>bn</td><td class="formula">∃y∃z∀x((Fx→Gy)∧(Gz→Fx))→∀x∃y(Fy↔Gy)</td><td></td></tr>

<tr><td>conpos1</td><td class="formula">∀y(Iy→∀x(Px↔Cxy))→∀x(Px↔∀y(Iy→Cxy))</td><td></td></tr>

<tr><td>conpos2</td><td class="formula">∀x(Px↔∀y(Iy→Cxy))→∀y(Iy→∀x(Px↔Cxy))</td><td></td></tr>

<tr><td>infinity</td><td class="formula">¬(∀x∃yFxy ∧ ∀x∀y∀z(Fxy∧Fyz→Fxz) ∧ ∀x¬Fxx)</td><td></td></tr>

</table>
    
<script type="text/javascript">

var tests = [];
document.querySelectorAll('.formula').forEach(function(td) {
    var formula = td.innerHTML;
    var resTd = td.parentNode.childNodes[2];
    td.onclick = function(e) {
        prove(td.innerHTML, resTd);
    }
    tests.push(td.onclick);
});

var prover;
var stopTimer;
var provingAll;
function prove(fla, resEl) {
    var parser = new Parser();
    var formula = parser.parseFormula(fla);
    console.log('testing '+fla);
    var startTime = performance.now();
    prover = new Prover([formula.negate()], parser);
    prover.onfinished = function(status) {
        var endTime = performance.now();
        console.log('done with '+fla);
        var res = (endTime - startTime) + ":&nbsp;" + (status ? "valid" : "invalid");
        resEl.innerHTML = res;
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
Limit <input type="text" size="7" name="l" value="3000"> ms/test
</form>
</div>

</body>
</html>
