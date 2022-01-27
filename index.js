
// This file deals with the user interface.

var flaFieldValue = '';
function updateInput() {
    // called on page load and keyup events to render symbols and toggle the
    // accessibility row
    var ostr = document.forms[0].flaField.value;
    if (ostr == flaFieldValue) {
        // no change; e.g. curser moved to highlight part of formula
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
    str = str.replace(/&|\^| and/ig, '∧');
    str = str.replace(/ v | or/ig, ' ∨ '); // 'v' letter => or symbol
    str = str.replace(/~| not/ig, '¬');
    str = str.replace(/<->|<=>| iff/ig, '↔');
    str = str.replace(/->|=>| then/g, '→');
    str = str.replace(/\[\]/g, '□');
    str = str.replace(/<>|◊/g, '◇');
    str = str.replace(/!|Ɐ/g, '∀');
    str = str.replace(/\?/g, '∃');
    str = str.replace(/\(A([s-z])\)/g, '∀$1'); // (Ax) => ∀x
    str = str.replace(/\(E([s-z])\)/g, '∃$1'); // (Ex) => ∃x
    str = str.replace(/(?:^|\W)\(([s-z])\)/g, '∀$1'); // (x) => ∀x, but not f(x) => f∀x
    str = str.replace(/\\?forall[\{ ]?\}?/g, '∀');
    str = str.replace(/\\?exists[\{ ]?\}?/g, '∃');
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
    }
    catch (e) {
        if (input.indexOf('v') > -1) {
            e += "\nIf you mean disjunction by the letter 'v', put a space on either side.";
        }
        alert(e);
        return false;
    }
    var premises = parsedInput[0];
    var conclusion = parsedInput[1];
    var initFormulas = premises.concat([conclusion.negate()]);
    document.getElementById("intro").style.display = "none";
    document.getElementById("model").style.display = "none";
    document.getElementById("rootAnchor").style.display = "none";
    document.getElementById("backtostartpage").style.display = "block";
    document.getElementById("status").style.display = "block";
    document.getElementById("statusmsg").innerHTML = "something went wrong: please email wo@umsu.de and tell me what you did";
    document.getElementById("statusbtn").style.display = "block";
    document.getElementById("statusbtn").innerHTML = "stop";
    
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
        document.getElementById("statusmsg").innerHTML = summary;
        document.getElementById("statusbtn").style.display = "none";
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
        // Start painting the tree:
        document.getElementById("rootAnchor").style.display = "block";
        self.painter = new TreePainter(sentree, document.getElementById("rootAnchor"));
        self.painter.finished = function() { addExportButtons(); }
        self.painter.paintTree();
    }
    prover.status = function(txt) {
        document.getElementById("statusmsg").innerHTML = txt;
    }
    setTimeout(function(){
        prover.start();
    }, 1);
    return false;
}

document.getElementById("statusbtn").onclick = function(e) {
    // handle clicks on 'stop'/'continue' button
    var btn = document.getElementById("statusbtn");
    if (btn.innerText == 'stop') {
        btn.innerText = 'continue';
        prover.stop();
    }
    else {
        btn.innerText = 'stop';
        prover.start();
    }
}
   
onload = function(e) {
    // in case the browser has automatically filled in some value into the
    // field (e.g. on reload):
    updateInput();
    // register event handlers:
    document.forms[0].flaField.onkeyup = updateInput;
    document.forms[0].onsubmit = function(e) {
        setTimeout(function() {
            setHash();
            startProof();
        }, 1);
        return false;
    }
    // start proof submitted via URL (e.g. from back button):
    if (location.search.startsWith('?f=')) {
        location.hash = location.search.substring(3);
        hashChange();
    }
    else if (location.hash.length > 0) {
        hashChange();
    }
    document.forms[0].flaField.focus();
}

var hashSetByScript = false;
function setHash() {
    // store input in URL when submitting the form:
    hashSetByScript = true; // prevent hashChange()
    var hash = encodeInputToHash(document.forms[0].flaField.value);
    if (document.getElementById('accessibilitySpan').style.display != 'none') {
        var accessibilityConstraints = [];
        document.querySelectorAll('.accCheckbox').forEach(function(el) {
            if (el.checked) {
                accessibilityConstraints.push(el.id);
            }
        });
        if (accessibilityConstraints.length > 0) {
            hash += '||'+accessibilityConstraints.join('|');
        }
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
        var hash = location.hash.replace(/%7C/g, '|');
        var hashparts = hash.split('||');
        document.forms[0].flaField.value = decodeHashToInput(hashparts[0].substring(1));
        var accessibilityConstraints = hashparts[1] ? hashparts[1].split('|') : [];
        document.querySelectorAll('.accCheckbox').forEach(function(el) {
            el.checked = accessibilityConstraints.includes(el.id); 
        });
        toggleAccessibilityRow();
        startProof();
    }
}

function encodeInputToHash(input) {
    /**
     * convert the string in the input field into something that can safely be
     * put in the URL
     */
    var symbols = ' ∧∨¬↔→∀∃□◇';
    inputNoSpaces = input.replace(/\s/g, '');
    var hash = inputNoSpaces.replace(new RegExp('['+symbols+']', 'g'), function(match) {
        return '~'+symbols.indexOf(match);
    });
    return hash;
}

function decodeHashToInput(hash) {
    /**
     * invert encodeInputToHash
     */
    if (hash.indexOf('%') > -1) {
        // old way of specifing input in URL hash, and use of unusual symbols
        hash = decodeURIComponent(hash.replace(/\+/g, '%20'));
    }
    var symbols = ' ∧∨¬↔→∀∃□◇';
    return hash.replace(/~./g, function(match) {
        return symbols[parseInt(match[1])];
    });
}

// functions to export tree as png:

function addExportButtons() {
    var el = document.createElement('div');
    el.id = 'exportDiv';
    el.style.position = 'absolute';
    var treeCoords = getTreeCoords();
    el.style.top = (treeCoords.bottom-treeCoords.top)/painter.scale + 'px';
    var width = (treeCoords.right-treeCoords.left)/painter.scale;
    el.style.width = width+'px';
    el.style.left = Math.round(width/-2) +'px'
    el.innerHTML = '<button onclick="exportImage()">save as png</button>';
    painter.rootAnchor.firstChild.appendChild(el);
}

function getTreeCoords() {
    // dict 'left', 'right', 'top', 'bottom'
    rootCoords = document.getElementById('rootAnchor').getBoundingClientRect();
    var treeCoords = {
        left: rootCoords.left,
        right: rootCoords.right,
        top: rootCoords.top,
        bottom: rootCoords.bottom
    };
    document.querySelectorAll('.treeNode').forEach(function(el) {
        var coords = el.getBoundingClientRect();
        if (coords.left < treeCoords.left) treeCoords.left = Math.round(coords.left);
        if (coords.right > treeCoords.right) treeCoords.right = Math.round(coords.right);
        if (coords.bottom > treeCoords.bottom) treeCoords.bottom = Math.round(coords.bottom);
    });
    log('tree coords: '+treeCoords.top+','+treeCoords.right+','+treeCoords.bottom+','+treeCoords.left);
    return treeCoords;
}

function getTreeHTML() {
    // returns HTML of tree, in idiosyncratic browser format. E.g., in Firefox
    // outerHTML does not include the dynamically set style properties for
    // position of subelements, instead it includes non-standard 'inset'
    // properties. To export cross-browser suitable HTML, we could add a
    // 'data-style' attribute to all elements whose value we set to the computed
    // style; after collecting rootAnchor.outerHTML, we could then rename that
    // attribute to 'style'. But the present code is sufficient for generating
    // an image.
    var root = document.getElementById('rootAnchor');
    // Note: inner/outerHTML does not include default styles from style.css; so
    // we have to add these; window.getComputedStyle() returns all style
    // properties, we only want the non-default ones.
    defaultStyles = {
        'DIV' : getDefaultStyle('div'),
        'SPAN' : getDefaultStyle('span')
    }
    document.querySelectorAll('#rootAnchor *').forEach(function(el) {
        var computedStyle = window.getComputedStyle(el);
        var defaultStyle = defaultStyles[el.tagName];
        if (!defaultStyle) return;
        for (var i=0; i<computedStyle.length; i++) {
            var cssProperty = computedStyle[i];
            var cssValue = computedStyle.getPropertyValue(cssProperty);
            if (defaultStyle[cssProperty] != computedStyle[cssProperty]) {
                el.style[cssProperty] = cssValue;
            }
        }
    });
    document.getElementById('exportDiv').style.display = 'none';
    var html = root.outerHTML;
    document.getElementById('exportDiv').style.display = 'block';
    // adjust location of root element:
    var treeCoords = getTreeCoords();
    var width = treeCoords.right - treeCoords.left;
    html = html.replace(/id="rootAnchor".+?>/, 'id="rootAnchor" style="position:relative; left:'+(width/2)+'px;">');
    return html;
}

function getDefaultStyle(tagName) {
    var defaultStyle = {};
    var element = document.body.appendChild(document.createElement(tagName));
    var computedStyle = window.getComputedStyle(element);
    for (var i=0; i < computedStyle.length; i++) {
        defaultStyle[computedStyle[i]] = computedStyle[computedStyle[i]];
    }
    document.body.removeChild(element);
    return defaultStyle;
}

function exportImage() {
    log('converting tree to image')
    // To create the image, we first need to move the external google fonts inline:
    if (!document.getElementById('localfontstyle')) {
        document.getElementsByTagName("head")[0].insertAdjacentHTML(
            "beforeend",
            '<link rel="stylesheet" id="localfontstyle" href="font.css" onload="exportImage()" type="text/css" />');
        return;
    }
    var canvas = document.createElement('canvas');
    var ctx = canvas.getContext('2d');
    var treeCoords = getTreeCoords();
    width = treeCoords.right - treeCoords.left;
    height = treeCoords.bottom - treeCoords.top;
    canvas.width = width;
    canvas.height = height;
    var tempImg = document.createElement('img');
    tempImg.addEventListener('load', function(el) {
        ctx.drawImage(el.target, 0, 0);
        var dataURL = canvas.toDataURL('image/png');
        var downloadLink = document.createElement('a');
        downloadLink.setAttribute('download', 'proof.png');
        var url = dataURL.replace(/^data:image\/png/, 'data:application/octet-stream');
        downloadLink.setAttribute('href', url);
        downloadLink.click();
        document.body.removeChild(downloadLink);
    });
    tempImg.addEventListener('error', function(el) {
        alert("sorry, this doesn't seem to work in your browser");
    });
    var html = getTreeHTML();
    html = html.replace(/<br>/g, '<br/>');
    var style = '';
    var cssRules = document.styleSheets[2].cssRules;
    for (var i=0; i<cssRules.length; i++) {
        style += cssRules[i].cssText;
    }
    xml = '<svg xmlns="http://www.w3.org/2000/svg" width="'+width+'" height="'+height+'">'
    xml += '<defs><style>' + style + '</style></defs>';
    xml += '<foreignObject width="100%" height="100%"><div xmlns="http://www.w3.org/1999/xhtml">'+html+'</div></foreignObject>';
    xml += '</svg>'
    log('<xmp>'+xml+'</xmp>');
    tempImg.src = 'data:image/svg+xml,' + encodeURIComponent(xml);
}
