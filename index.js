
// This file deals with the user interface of index.html.

function updateInput() {
    // replaces LaTeX commands for logical symbols by what is set in translator.logSymbols
    var ostr = document.forms[0].flaField.value;
    cposition = this.selectionStart;
    str = latex2str(ostr);  
    var diff = ostr.length - str.length
    document.forms[0].flaField.value = str;
    this.selectionEnd = cposition - diff;
}

function latex2str(str) {
    str = str.replace(/\s*/g, '');
    str = str.replace(/\\forall[\{ ]?\}?/g, '∀');
    str = str.replace(/\\exists[\{ ]?\}?/g, '∃');
    str = str.replace(/(\\neg|\\lnot)[\{ ]?\}?/g, '¬');
    str = str.replace(/\\Box[\{ ]?\}?/g, '□');
    str = str.replace(/\\Diamond[\{ ]?\}?/g, '◇');
    str = str.replace(/(\\vee|\\lor)[\{ ]?\}?/g, '∨');
    str = str.replace(/(\\wedge|\\land)[\{ ]?\}?/g, '∧');
    str = str.replace(/(\\to|\\rightarrow)[\{ ]?\}?/g, '→');
    str = str.replace(/\\leftrightarrow[\{ ]?\}?/g, '↔');
    //str = str.replace(/([^'])(\\[^<]*)/, '$1<span class="latex">$2</span>'); // unfinished latex commands
    //str = str.replace(/^(\\[^<]*)/, '<span class="latex">$1</span>'); // unfinished latex commands
    str = str.replace(/([^'])(\\[^<]*)/, '$1$2'); // unfinished latex commands
    str = str.replace(/^(\\[^<]*)/, '$1'); // unfinished latex commands
    return str;
}
// in case the browser has automatically filled in some value into the
// field (e.g. on Reload):
setTimeout(updateInput, 1000);

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
   
    document.forms[0].flaField.onkeyup = updateInput;

    // insert the symbol buttons on top of the text field:
    var symButtons = ['¬','∧','∨','→','↔','∀','∃','□','◇'];
    for (var i=0; i<symButtons.length; i++) {
        var div = document.createElement("div");
        div.className = "symbutton";
        div.innerHTML = symButtons[i];
        div.onmousedown = function(e) { this.style.borderStyle = "inset"; }
        div.onmouseup = div.onmouseout = function(e) { this.style.borderStyle = "outset"; }
        div.onclick = symButtonClick;
        document.getElementById("symboltd").appendChild(div);
    }
    
    function symButtonClick(e) {
        var field = document.forms[0].flaField;
        var command = this.innerHTML;
        field.insertAtCaret(command);
    }
    
    document.forms[0].onsubmit = function(e) {
        // The action begins...
        var parser = new Parser();
        try {
            var formula = parser.parseFormula(this.flaField.value);
        }
        catch (e) {
            alert(e);
            return false;
        }
        document.getElementById("intro").style.display = "none";
        document.getElementById("model").style.display = "none";
        document.getElementById("rootAnchor").style.display = "none";
        document.getElementById("statusBox").style.display = "block";
        document.getElementById("statusHeader").innerHTML = "Proving...";
        document.getElementById("statusStop").style.display = "inline";
        document.getElementById("statusStop").firstChild.nodeValue = 'stop';
        document.getElementById("paintStop").firstChild.nodeValue = 'stop';
        // Now a free-variable tableau is created. When the proof is
        // finished, prover.finished() is called.
        var rootFormula = formula.negate();
        if (rootFormula.isModal()) {
            rootFormula = rootFormula.translateToModal();
        }
        rootFormula = rootFormula.normalize(); // xxx should I do this in Prover? currently in both!
        var prover = new Prover([rootFormula]);
        prover.status = function(str) {
            // The prover dumps status messages to this function. 
            document.getElementById("status").innerHTML = str;
        }
        prover.onfinished = function(treeClosed) {
            // The prover has finished.
            document.getElementById("statusHeader").innerHTML = "<span class='formula'>" + formula + "</span> is " + (treeClosed ? "valid." : "invalid.");
            document.getElementById("statusStop").style.display = "none";
            prover.status("");
            // Translate the free-variable tableau into a sentence tableau:
            var sentenceTree = new SenTree(this.tree, [formula.negate()]);
            if (!treeClosed) {
                // Tree is open. Display a countermodel if one is known:
                if (!this.counterModel) this.counterModel = sentenceTree.getCounterModel();
                if (this.counterModel) {
                    document.getElementById("model").style.display = "block";
                    document.getElementById("model").innerHTML = "<b>Countermodel:</b><br>" + this.counterModel;
                    return; // shouldn't display tree because if the model was found by the modelFinder, the tree is unfinished
                }
            }
            // Start painting the tree:
            document.getElementById("rootAnchor").style.display = "block";
            document.getElementById("paintBar").style.display = "block";
            self.painter = new TreePainter(sentenceTree, document.getElementById("rootAnchor"));
            self.painter.finished = function() {
                document.getElementById("paintBar").style.display = "none";
            }
            self.painter.paintTree();
        }
        setTimeout(function(){
            prover.start();
        }, 1);
        return false;
    }
   
    // event handlers for the buttons that control the proving/painting:
    
    document.getElementById("statusStop").onclick = function(e) {
        if (this.firstChild.nodeValue == 'stop') {
            prover.stop();
            this.firstChild.nodeValue = 'continue';
            return;
        }
        this.firstChild.nodeValue = 'stop';
        prover.nextStep();
    }
    
    document.getElementById("paintStop").onclick = function(e) {
        if (this.firstChild.nodeValue == 'stop') {
            painter.stop();
            this.firstChild.nodeValue = 'continue';
            return;
        } 
        this.firstChild.nodeValue = 'stop';
        painter.paintTree();
    }
    
    document.getElementById("paintFaster").onclick = function(e) {
        if (this.firstChild.nodeValue == 'faster') {
            painter.oldInterval = painter.paintInterval;
            painter.paintInterval = 100;
            this.firstChild.nodeValue = 'slower';
            return;
        }
        painter.paintInterval = painter.oldInterval;
        this.firstChild.nodeValue = 'faster';
    }
    
    // prove formula submitted via URL:
    if (location.search.match(/\?f=/)) {
        document.forms[0].flaField.value = unescape(location.search.substr(3));
        document.forms[0].onsubmit();
    }
}
