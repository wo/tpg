function TreePainter(senTree, rootAnchor) {
    // Constructor for a tree painter. rootAnchor is the HTML element into which
    // the tree will be written.

    this.paintInterval = 200;      // number of ms between paint steps
    this.branchPadding = window.innerWidth < 500 ? 0 :
        window.innerWidth < 800 ? 20 : 30; // min margin between tree branches
    this.branchingHeight = 40;     // vertical space used by branching lines
    this.nodeHiParentCSS = "treeNodeHiParent" // CSS class for nodes that are currently expanded
    this.nodeHiChildCSS = "treeNodeHiChild"   // CSS class for nodes that are currently added
    
    this.tree = senTree;
    this.isModal = senTree.parser.isModal;
    this.rootAnchor = rootAnchor;
    this.rootAnchor.innerHTML = "";
    this.minX = this.branchPadding/2 - rootAnchor.offsetLeft;
    this.scale = 1;
    
    this.curNodeNumber = 0;
    this.highlighted = [];

}

TreePainter.prototype.paintTree = function() {
    // start painting
    var node = this.getNextUnpaintedNode();
    if (!node) {
        this.highlightNothing();
        return this.finished();
    }
    var paintNodes = this.tree.getExpansion(node);
    log("expansion: " + paintNodes);
    for (var i=0; i<paintNodes.length; i++) {
        this.paint(paintNodes[i]);
    }
    this.highlight(paintNodes, node.fromNodes);

    this.paintTimer = setTimeout(function(){
        this.paintTree();
    }.bind(this), this.paintInterval);
}

TreePainter.prototype.stop = function() {
    clearTimeout(this.paintTimer);
}

TreePainter.prototype.finished = function() {
}

TreePainter.prototype.paint = function(node) {
    // paint single node
    if (!node.parent || node.parent.children.length == 2) {
        node.container = this.makeContainer(node);
    }
    else {
        node.container = node.parent.container;
    }
    log("painting "+node+" in "+node.container.str);
    // create node div
    node.div = this.makeNodeDiv(node);
    node.container.appendChild(node.div);

    // Since all children of the container are absolutely positioned, the
    // container element is actually a horizontal line starting centered at
    // the top of the branch.
    log('w '+node.formulaSpan.offsetWidth);
    node.div.style.top = node.container.h + "px";
    node.container.h += node.div.offsetHeight + 3; // that number is the line-spacing
    if (node.children.length == 0) {
        // add some spacing below leaf nodes
        node.container.h += this.branchPadding;
    }
    if (node.formulaSpan.offsetWidth > node.container.formulaWidth) {
        node.container.formulaWidth = node.formulaSpan.offsetWidth + 10;
        log('adjusting container width '+node.container.formulaWidth);
        var n = node;
        do {
            n.formulaSpan.style.width = node.container.formulaWidth + "px";
            n.div.style.left = -node.div.offsetWidth/2 + "px";
            n = n.parent;
        } while (n && n.container == node.container);
    }
    else {
        log('using old container width '+node.container.formulaWidth);
        node.formulaSpan.style.width = node.container.formulaWidth + "px";
        node.div.style.left = -node.container.w/2 + "px";
    }
    // node.div.style.left = -node.div.offsetWidth/2 + "px";
    node.container.w = Math.max(node.container.w, node.div.offsetWidth);
    this.repositionBranches(node);
    this.keepTreeInView();
}

TreePainter.prototype.makeContainer = function(node) {
    // create new container for subbranch
    log('creating new container');
    var parContainer = node.parent ? node.parent.container : this.rootAnchor;
    var container = document.createElement('div');
    parContainer.appendChild(container);
    if (node.parent) parContainer.subContainers.push(container);
    container.subContainers = [];
    container.style.width = "100%";
    container.style.position = "absolute";
    container.style.left = "0px";
    container.style.top = node.parent ? parContainer.h + this.branchingHeight + "px" : "0px";
    container.w = container.h = 0;
    container.str = "{ "+node+ " }" + (self.__strid ? self.__strid++ : (self.__strid = 1));
    container.formulaClass = 'fla'+this.curNodeNumber;
    container.formulaWidth = 0;
    return container;
}

TreePainter.prototype.makeNodeDiv = function(node) {
    var div = document.createElement('div');
    div.className = 'treeNode';

    var nodeNumberSpan = document.createElement('span');
    node.nodeNumber = ++this.curNodeNumber;
    nodeNumberSpan.className = 'nodenumber';
    nodeNumberSpan.innerHTML = node.nodeNumber+'.';
    div.appendChild(nodeNumberSpan);
    
    node.formulaSpan = document.createElement('span');
    node.formulaSpan.className = 'formula '+node.container.formulaClass;
    node.formulaSpan.innerHTML = node.formula.string;
    if (node.closedEnd) node.formulaSpan.innerHTML += "<br><b>x</b>";
    div.appendChild(node.formulaSpan);
    
    if (this.isModal) {
        var worldSpan = document.createElement('span');
        worldSpan.className = 'worldlabel';
        worldSpan.innerHTML = node.formula.world ? '('+node.formula.world+')' : '';
        div.appendChild(worldSpan);
    }

    var fromSpan = document.createElement('span');
    fromSpan.className = 'fromnumbers';
    var annot = node.fromNodes.map(function(n) { return n.nodeNumber; });
    if (node.fromRule) {
        var fromRule = node.fromRule.toString().substr(0,3);
        if (!['alp', 'bet', 'gam', 'del', 'mod'].includes(fromRule)) {
            annot.push(fromRule+'.');
        }
    }
    fromSpan.innerHTML = annot.length>0 ? "("+annot.join(',')+")" : " ";
    div.appendChild(fromSpan);

    return div;
}

TreePainter.prototype.repositionBranches = function(node) {
    var par = node.container;
    while ((par = par.parentNode).subContainers) {
        if (!par.subContainers[1]) continue;
        var overlap = this.getOverlap(par);
        //log("comparing subcontainers for overlap: " + par.str);
        if (overlap) {
            log(overlap+" overlap between "+par.subContainers[0].str+" and "+par.subContainers[1].str);
            var x1 = parseInt(par.subContainers[0].style.left) - Math.ceil(overlap/2);
            var x2 = parseInt(par.subContainers[1].style.left) + Math.ceil(overlap/2);
            par.subContainers[0].style.left = x1 + "px";
            par.subContainers[1].style.left = x2 + "px";
            if (par.branchLines) {
                for (var i=0; i<par.branchLines.length; i++) {
                    par.removeChild(par.branchLines[i]);
                }
            }
            var centre = this.isModal ? -8 : 0; // hack to make branching lines look more centred
            var line1 = this.drawLine(par, centre, par.h, x1+centre, par.h + this.branchingHeight-2);
            var line2 = this.drawLine(par, centre, par.h, x2+centre, par.h + this.branchingHeight-2);
            par.branchLines = [line1, line2];
            // now that sub0 has been moved left, it may itself overlap
            // something, so we continue the loop
        }
    }
}

TreePainter.prototype.getOverlap = function(par) {
    var overlap = 0;
    // compare all pairs of sub(sub...)Containers:
    var co1, co2, co1s = [par.subContainers[0]], co2s;
    par.__x = 0; par.__y = 0;
    while ((co1 = co1s.shift())) {
        co2s = [par.subContainers[1]];
        while ((co2 = co2s.shift())) {
            co1.__x = co1.parentNode.__x + parseInt(co1.style.left);// - co1.w/2;
            co1.__y = co1.parentNode.__y + parseInt(co1.style.top);
            co2.__x = co2.parentNode.__x + parseInt(co2.style.left);// - co2.w/2;
            co2.__y = co2.parentNode.__y + parseInt(co2.style.top);
            if ((co1.__y >= co2.__y) && (co1.__y < co2.__y + co2.h) ||
                (co2.__y >= co1.__y) && (co2.__y < co1.__y + co1.h)) { // y-overlap > 0
                var overlap12 = (co1.__x + co1.w/2 + painter.branchPadding) - (co2.__x - co2.w/2);
                overlap = Math.max(overlap, overlap12);
            }
            co2s = co2s.concat(co2.subContainers);
        }
        co1s = co1s.concat(co1.subContainers);
    }
    return Math.floor(overlap);
}

TreePainter.prototype.keepTreeInView = function() {
    var mainContainer = this.rootAnchor.firstChild;
    // check if tree fits horizontal display width:
    if (mainContainer.getBoundingClientRect) {
        var midPoint = Math.round(mainContainer.getBoundingClientRect()['left']);
        var winTreeRatio = window.innerWidth*1.0/(midPoint*2);
        if (winTreeRatio < 1) {
            this.scale = Math.max(winTreeRatio, 0.8);
            document.getElementById('rootAnchor').style.transform="scale("+this.scale+")";
            log("tree doesn't fit: ratio window.width/tree.width "+winTreeRatio);
        }
    }
    var minX = this.getMinX();
    if (minX < this.minX/this.scale) {
        var invisibleWidth = (this.minX/this.scale - minX);
        log("minX " + minX + "<" + this.minX+": tree out of left document border by " + invisibleWidth);
        mainContainer.style.left = mainContainer.__x + invisibleWidth + "px";
    }
}

TreePainter.prototype.getMinX = function() {
    // get x-position of leftmost container (relative to rootAnchor)
    var minX = 0;
    var con, cons = [this.rootAnchor.firstChild];
    while ((con = cons.shift())) {
        con.__x = (con.parentNode.__x || 0) + parseInt(con.style.left);
        if (con.__x - con.w/2 < minX) {
            minX = con.__x - con.w/2;
        }
        cons = cons.concat(con.subContainers);
    }
    return minX;
}

TreePainter.prototype.highlight = function(children, fromNodes) {
    while (this.highlighted.length) {
        this.highlighted.shift().div.style.backgroundColor = 'unset';
    }
    for (var i=0; i<children.length; i++) {
        // children[i].div.className = 'treeNodeHiChild';
        children[i].div.style.backgroundColor = '#00708333';

    }
    for (var i=0; i<fromNodes.length; i++) {
        // fromNodes[i].div.className = 'treeNodeHiParent';
        fromNodes[i].div.style.backgroundColor = '#00708366';
    }
    this.highlighted = children.concat(fromNodes);
}

TreePainter.prototype.highlightNothing = function() {
    this.highlight([], []);
}

TreePainter.prototype.drawLine = function(el, x1, y1, x2, y2) {
    // adapted from https://stackoverflow.com/questions/4270485/drawing-lines-on-html-page
    log('line in '+el+' from '+x1+'/'+y1+' to '+x2+'/'+y2);
    var a = x1 - x2;
    var b = y1 - y2;
    var length = Math.sqrt(a*a + b*b);
    var sx = (x1 + x2) / 2
    var x = sx - length / 2;
    var y = (y1 + y2) / 2;
    var angle = Math.PI - Math.atan2(-b, a);
    var line = document.createElement("div");
    var styles = 'border: 1px solid #678; '
               + 'width: ' + length + 'px; '
               + 'height: 0px; '
               + '-moz-transform: rotate(' + angle + 'rad); '
               + '-webkit-transform: rotate(' + angle + 'rad); '
               + '-o-transform: rotate(' + angle + 'rad); '  
               + '-ms-transform: rotate(' + angle + 'rad); '  
               + 'position: absolute; '
               + 'top: ' + y + 'px; '
               + 'left: ' + x + 'px; ';
    line.setAttribute('style', styles);  
    el.appendChild(line);
    return line;
}

TreePainter.prototype.getNextUnpaintedNode = function() {
    var nodes = [this.tree.nodes[0]];
    var node;
    while ((node = nodes.shift())) {
        do {
            if (!node.div) return node;
            if (node.children.length == 2) nodes.unshift(node.children[1]);
        } while ((node = node.children[0]));
    }
    return null;
}
    
