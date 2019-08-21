
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

onload = function(e) {
   
    // in case the browser has automatically filled in some value into the
    // field (e.g. on Reload):
    updateInput();

    document.forms[0].flaField.onkeyup = updateInput;

    // insert the symbol buttons on top of the text field:
    var symButtons = ['¬','∧','∨','→','↔','∀','∃','□','◇'];
    for (var i=0; i<symButtons.length; i++) {
        var div = document.createElement("div");
        div.className = "symbutton button formula";
        div.innerHTML = symButtons[i];
        div.onclick = symButtonClick;
        document.getElementById("symbolButtons").appendChild(div);
    }

    function symButtonClick(e) {
        var field = document.forms[0].flaField;
        var command = this.innerHTML;
        field.insertAtCaret(command);
        toggleAccessibilityRow();
    }

    // make example formulas clickable:
    var ul = document.getElementById('exampleList');
    for (var i=0; i<ul.childNodes.length; i++) {
        ul.childNodes[i].onclick = function(e) {
            document.forms[0].flaField.value = this.innerHTML;
            document.forms[0].onsubmit();
            return false;
        }
    }

    var prover;
    document.forms[0].onsubmit = function(e) {
        // The action begins...
        var parser = new Parser();
        try {
            var parsedInput = parser.parseInput(this.flaField.value);
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
        document.getElementById("status").innerHTML = "<div id='working'>working</div>";

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
                var summary = conclusion + " is " + (treeClosed ? "valid." : "invalid.");
            }
            else {
                var summary = premises.map(function(f){
                    return "<span class='formula'>"+f+"</span>";
                }).join(', ') + (treeClosed ? " entails " : " does not entail ") + conclusion + ".";
            }
            document.getElementById("status").innerHTML = summary;
            // Translate the free-variable tableau into a sentence tableau:
            var sentree = new SenTree(this.tree, parser);
            if (!treeClosed) {
                // Tree is open. Display a countermodel if one is known:
                if (!this.counterModel) this.counterModel = sentree.getCounterModel();
                if (this.counterModel) {
                    document.getElementById("model").style.display = "block";
                    document.getElementById("model").innerHTML = "<b>Countermodel:</b><br>" +
                        this.counterModel.toHTML();
                    return; // shouldn't display tree because if the model was found by the modelfinder, the tree is unfinished
                }
            }
            if (parser.isModal) {
                sentree.modalize();
            }
            // Start painting the tree:
            document.getElementById("rootAnchor").style.display = "block";
            self.painter = new TreePainter(sentree, document.getElementById("rootAnchor"));
            self.painter.paintTree();
        }
        setTimeout(function(){
            prover.start();
        }, 1);
        return false;
    }
   
    // prove formula submitted via URL:
    if (location.search.match(/\?f=/)) {
        document.forms[0].flaField.value = unescape(location.search.substr(3));
        document.forms[0].onsubmit();
    }
}
