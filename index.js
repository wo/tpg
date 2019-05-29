
// This file deals with the user interface of index.html.

function laTeX2html(str) {
   // replaces LaTeX commands for logical symbols by what is set in translator.logSymbols
   str = str.replace(/\s*/g, '');
   str = str.replace(/\\forall[\{ ]?\}?/g, translator.logSymbols[tc.ALL]);
   str = str.replace(/\\exists[\{ ]?\}?/g, translator.logSymbols[tc.SOME]);
   str = str.replace(/(\\neg|\\lnot)[\{ ]?\}?/g, translator.logSymbols[tc.NOT]);
   str = str.replace(/\\Box[\{ ]?\}?/g, translator.logSymbols[tc.BOX]);
   str = str.replace(/\\Diamond[\{ ]?\}?/g, translator.logSymbols[tc.DIAMOND]);
   str = str.replace(/(\\vee|\\lor)[\{ ]?\}?/g, translator.logSymbols[tc.OR]);
   str = str.replace(/(\\wedge|\\land)[\{ ]?\}?/g, translator.logSymbols[tc.AND]);
   str = str.replace(/(\\to|\\rightarrow)[\{ ]?\}?/g, translator.logSymbols[tc.THEN]);
   str = str.replace(/\\leftrightarrow[\{ ]?\}?/g, translator.logSymbols[tc.IFF]);
   str = str.replace(/([^'])(\\[^<]*)/, '$1<span class="latex">$2</span>'); // unfinished latex commands
   str = str.replace(/^(\\[^<]*)/, '<span class="latex">$1</span>'); // unfinished latex commands
   return str;
}

document.forms[0].flaField.onkeyup = renderFormula;

function renderFormula() {
   var field = document.forms[0] && document.forms[0].flaField;
   if (field) {
      document.getElementById("renderedFla").innerHTML = laTeX2html(field.value);
   }
   setTimeout(renderFormula, 1000);
}

// in case the browser has automatically filled in some value into the
// field (e.g. on Reload):
setTimeout(renderFormula, 1000);

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
   renderFormula();
}


onload = function(e) {
   
   // insert the symbol buttons on top of the text field:
   var symButtons = [tc.NOT, tc.AND, tc.OR, tc.THEN, tc.IFF, tc.ALL, tc.SOME];
   for (var i=0; i<symButtons.length; i++) {
      var div = document.createElement("div");
      div.className = "symbutton";
      div.innerHTML = translator.logSymbols[symButtons[i]];
      div.onmousedown = function(e) { this.style.borderStyle = "inset"; }
      div.onmouseup = div.onmouseout = function(e) { this.style.borderStyle = "outset"; }
      div.onclick = symButtonClick;
      document.getElementById("symboltd").appendChild(div);
   }
   
   function symButtonClick(e) {
      var field = document.forms[0].flaField;
      var command = this.firstChild.getAttribute("alt");
      field.insertAtCaret(command);
   }
   
   document.forms[0].onsubmit = function(e) {
      // The action begins...
      try {
         translator.init();
         var formula = translator.latex2fla(this.flaField.value);
         if (!formula) {
            alert("Invalid formula.\n"+translator.error);
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
         // Now a free-variable tableau is created. When the proof is finished, prover.finished() is called.
         prover.start(formula.negate());
      }
      catch (e) {
         alert("Error: " + e);
      };
      return false;
   }
   
   prover.status = function(str) {
      // The prover dumps status messages to this function. 
      document.getElementById("status").innerHTML = str;
   }
   
   prover.finished = function(treeClosed) {
      // The prover has finished.
      document.getElementById("statusHeader").innerHTML = "<span class='formula'>" + translator.fla2html(this.formula[1]) + "</span> is " + (treeClosed ? "valid." : "invalid.");
      document.getElementById("statusStop").style.display = "none";
      prover.status("");
      // Translate the free-variable tableau into a sentence tableau:
      var sentenceTree = new SenTree(this.tree);
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
