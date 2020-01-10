
// This file deals with the user interface of index.html.

var flaFieldValue = '';
function updateInput() {
    var ostr = document.forms[0].flaField.value;
    if (ostr == flaFieldValue) {
        // e.g. curser moved to highlight part of formula
        return true;
    }
    cposition = this.selectionStart;
    flaFieldValue = renderSymbols(ostr);  
    var diff = ostr.length - flaFieldValue.length
    document.forms[0].flaField.value = flaFieldValue;
    this.selectionEnd = cposition - diff;
    toggleAccessibilityRow();
}

function renderSymbols(str) {
    str = str.replace('&', '∧');
    str = str.replace('^', '∧');
    str = str.replace('<->', '↔');
    str = str.replace('->', '→');
    str = str.replace('~', '¬');
    str = str.replace(' v ', ' ∨ '); // 'v' letter => or symbol
    str = str.replace('[]', '□');
    str = str.replace('<>', '◇');
    str = str.replace(/\(A([s-z])\)/, '∀$1'); // (Ax) => ∀x
    str = str.replace(/\(E([s-z])\)/, '∃$1'); // (Ex) => ∃x
    str = str.replace(/(?:^|\W)\(([s-z])\)/, '∀$1'); // (x) => ∀x, but not f(x) => f∀x
    str = str.replace(/\\forall[\{ ]?\}?/g, '∀');
    str = str.replace(/\\exists[\{ ]?\}?/g, '∃');
    str = str.replace(/(\\neg|\\lnot)[\{ ]?\}?/g, '¬');
    str = str.replace(/(\\vee|\\lor)[\{ ]?\}?/g, '∨');
    str = str.replace(/(\\wedge|\\land)[\{ ]?\}?/g, '∧');
    str = str.replace(/(\\to|\\rightarrow)[\{ ]?\}?/g, '→');
    str = str.replace(/\\leftrightarrow[\{ ]?\}?/g, '↔');
    str = str.replace(/\\[Bb]ox[\{ ]?\}?/g, '□');
    str = str.replace(/\\[Dd]iamond[\{ ]?\}?/g, '◇');
    return str;
}

function toggleAccessibilityRow() {
    if (/[□◇]/.test(document.forms[0].flaField.value)) {
        document.getElementById('accessibilitySpan').style.display = 'inline-block';
    }
    else {
        document.getElementById('accessibilitySpan').style.display = 'none';
    }
}

// define method to insert character at caret position upon button click: 
document.forms[0].flaField.insertAtCaret = function(str) {
   if (document.selection) {
      // Internet Explorer
      this.focus();
      sel = document.selection.createRange();
      sel.text = str;
      this.focus();
   }
   else if (this.selectionStart || this.selectionStart === 0) {
      // Firefox and Webkit
      var startPos = this.selectionStart;
      var endPos = this.selectionEnd;
      var scrollTop = this.scrollTop;
      var val = this.value; 
      this.value = val.substring(0, startPos)+str+val.substring(endPos,val.length);
      this.focus();
      this.selectionStart = startPos + str.length;
      this.selectionEnd = startPos + str.length;
      this.scrollTop = scrollTop;
   } 
   else {
      this.value += str;
      this.focus();
   }
}

document.querySelectorAll('.symbutton').forEach(function(el) {
    el.onclick = function(e) {
        var field = document.forms[0].flaField;
        var command = this.innerHTML;
        field.insertAtCaret(command);
        toggleAccessibilityRow();
    }
});

var prover = null;
function startProof() {
    var input = document.forms[0].flaField.value;
    var parser = new Parser();
    try {
        var parsedInput = parser.parseInput(input);
        var premises = parsedInput[0];
        var conclusion = parsedInput[1];
        var initFormulas = premises.concat([conclusion.negate()]);
    }
    catch (e) {
        alert(e);
        return false;
    }
    document.getElementById("intro").style.display = "none";
    document.getElementById("model").style.display = "none";
    document.getElementById("rootAnchor").style.display = "none";
    document.getElementById("backtostartpage").style.display = "block";
    document.getElementById("status").style.display = "block";
    document.getElementById("status").innerHTML = "something went wrong: please email wo@umsu.de and tell me what you did";
    
    // Now a free-variable tableau is created. When the proof is finished,
    // prover.finished() is called.
    var accessibilityConstraints = [];
    if (parser.isModal) {
        document.querySelectorAll('.accCheckbox').forEach(function(el) {
            if (el.checked) {
                // accFla = parser.parseAccessibilityFormula(el.value);
                accessibilityConstraints.push(el.id);
            }
        });
    }
    prover = new Prover(initFormulas, parser, accessibilityConstraints);
    prover.onfinished = function(treeClosed) {
        // The prover has finished. Show result:
        var conclusionSpan = "<span class='formula'>"+conclusion+"</span>";
        if (initFormulas.length == 1) {
            var summary = conclusionSpan + " is " + (treeClosed ? "valid." : "invalid.");
        }
        else {
            var summary = premises.map(function(f){
                return "<span class='formula'>"+f+"</span>";
            }).join(', ') + (treeClosed ? " entails " : " does not entail ") + conclusionSpan + ".";
        }
        document.getElementById("status").innerHTML = summary;
        // Translate the free-variable tableau into a sentence tableau:
        var sentree = new SenTree(this.tree, parser); 
        if (!treeClosed) {
            // Tree is open. Display a countermodel if one is known:
            // if (!this.counterModel) this.counterModel = sentree.getCounterModel();
            if (this.counterModel) {
                document.getElementById("model").style.display = "block";
                document.getElementById("model").innerHTML = "<b>Countermodel:</b><br>" +
                    this.counterModel.toHTML();
            }
            return; 
        }
        if (parser.isModal) {
            sentree.modalize();
        }
        // Start painting the tree:
        document.getElementById("rootAnchor").style.display = "block";
        self.painter = new TreePainter(sentree, document.getElementById("rootAnchor"));
        self.painter.paintTree();
    }
    prover.status = function(txt) {
        document.getElementById("status").innerHTML = txt;
    }
    setTimeout(function(){
        prover.start();
    }, 1);
    return false;
}
   
onload = function(e) {
    // in case the browser has automatically filled in some value into the
    // field (e.g. on reload):
    updateInput();
    // register event handlers:
    document.forms[0].flaField.onkeyup = updateInput;
    document.forms[0].onsubmit = function(e) {
        setHash();
        startProof();
        return false;
    }
    // start proof submitted via URL (e.g. from back button):
    if (location.hash.length > 0) {
        hashChange();
    }
}

var hashSetByScript = false;
function setHash() {
    // store input in URL when submitting the form:
    hashSetByScript = true; // prevent hashChange()
    var hash = document.forms[0].flaField.value;
    var accessibilityConstraints = [];
    document.querySelectorAll('.accCheckbox').forEach(function(el) {
        if (el.checked) {
            accessibilityConstraints.push(el.id);
        }
    });
    if (accessibilityConstraints.length > 0) {
        hash += '||'+accessibilityConstraints.join('|');
    }
    location.hash = hash;
}

window.onhashchange = hashChange;

function hashChange() {
    if (hashSetByScript) {
        hashSetByScript = false;
        return;
    }
    // input submitted via URL or through back button; in the second case there
    // might be a prover running.
    if (prover) prover.stop();
    if (location.hash.length == 0) {
        document.getElementById("intro").style.display = "block";
        document.getElementById("model").style.display = "none";
        document.getElementById("rootAnchor").style.display = "none";
        document.getElementById("backtostartpage").style.display = "none";
        document.getElementById("status").style.display = "none";
    }
    else {
        var hash = decodeURIComponent(location.hash.substr(1).replace(/\+/g, '%20'));
        var hashparts = hash.split('||');
        document.forms[0].flaField.value = hashparts[0];
        var accessibilityConstraints = hashparts[1] ? hashparts[1].split('|') : [];
        document.querySelectorAll('.accCheckbox').forEach(function(el) {
            el.checked = accessibilityConstraints.includes(el.id); 
        });
        toggleAccessibilityRow();
        startProof();
    }
}

