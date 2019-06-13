// 
// A TreePainter object takes a SenTree object and outputs it as a tree in HTML.
// Methods:
//    paintTree = function()          initiates/continues the painting
//    stop = function()               halts the painting
//    finished = function()           ic called when the painting has finished
// Some properties that influence the layout of the tree are defined at the beginning
// of the constructor.
//

function TreePainter(senTree, rootAnchor) {
    // Constructor for a tree painter. rootAnchor is the HTML element into which
    // the tree will be written.
    
    this.paintInterval = 700;      // number of ms between paint steps
    this.branchPadding = 30;       // min margin between tree branches
    this.branchingHeight = 40;     // vertical space used by branching lines
    this.pixelDistanceOnLine = 4;  // distance between pixels on the branching lines (1 = continuous)
    this.lineColor = "#600";
    this.formulaCSS = "formula";              // CSS class for formula <span>s
    this.nodeCSS = "treeNode";                // CSS class for tree node <div>s
    this.nodeHiParentCSS = "treeNodeHiParent" // CSS class for nodes that are currently expanded
    this.nodeHiChildCSS = "treeNodeHiChild"   // CSS class for nodes that are currently added
    
    this.tree = senTree;
    this.rootAnchor = rootAnchor;
    this.rootAnchor.innerHTML = "";
    this.minX = this.branchPadding - rootAnchor.offsetLeft;
    var curNodeNumber = 0;
    var freePixels = [];
    var highlighted = [];
    var painter = this;
    TreePainter.instance = this; // will break if several instances are simultanously in use (which never are)
    
    this.paintTree = function() {
        // start painting
        var node = getNextUnpainted(this.tree);
        if (!node) {
            this.highlight([]);
            return this.finished();
        }
        var paintNodes = this.tree.getExpansion(node);
        log("expansion: " + paintNodes);
        for (var i=0; i<paintNodes.length; i++) {
            this.paint(paintNodes[i]);
        }
        this.highlight(paintNodes, node.developedFrom);

        this.paintTimer = setTimeout(function(){
            TreePainter.instance.paintTree();
        }.bind(this), this.paintInterval);
    };
    
    this.stop = function() {
        clearTimeout(this.paintTimer);
    }
    
    this.finished = function() {}
    
    this.paint = function(node) {
        // paint single node
        if (!node.parent || node.parent.children.length == 2) {
            // create new container for subbranch:
            var parContainer = node.parent ? node.parent.container : this.rootAnchor;
            node.container = document.createElement('div');
            parContainer.appendChild(node.container);
            if (node.parent) parContainer.subContainers.push(node.container);
            node.container.subContainers = [];
            node.container.style.width = "100%";
            node.container.style.position = "absolute";
            node.container.style.left = "0px";
            node.container.style.top = node.parent ? parContainer.h + this.branchingHeight + "px" : "0px";
            node.container.w = node.container.h = 0;
            node.container.str = "{ "+node+ " }" + (self.__strid ? self.__strid++ : (self.__strid = 1));
        }
        else node.container = node.parent.container;
        log("painting "+node+" in "+node.container.str);
        // create node div and put it centered at the bottom of its container:
        node.nodeNumber = ++curNodeNumber;
        var html = curNodeNumber + ".&nbsp;&nbsp;<span class='" + this.formulaCSS + "'>" + node.formula.string + "</span>";
        html += node.developedFrom ? "&nbsp;&nbsp;(" + node.developedFrom.nodeNumber + ")" : "&nbsp;&nbsp;&nbsp;&nbsp;";
        if (node.closedEnd) html += "<br><b>x</b>";
        node.div = document.createElement('div');
        node.div.innerHTML = html;
        node.div.className = this.nodeCSS;
        node.div.style.position = "absolute";
        document.body.appendChild(node.div); // hack to get correct size
        node.div.w = node.div.offsetWidth;
        node.div.h = node.div.offsetHeight;
        document.body.removeChild(node.div);
        node.container.appendChild(node.div);
        // Since all children of the container are absolutely positioned, the
        // container element is actually a dot centered at the top of the branch.
        node.div.style.left = -node.div.w/2 + "px";
        node.div.style.top = node.container.h + "px";
        node.container.h += node.div.h + 3; // that number is the line-spacing
        if (node.children.length == 0) node.container.h += this.branchPadding;
        node.container.w = Math.max(node.container.w, node.div.w);
        // check if container overlaps some other container on its left:
        var par = node.container;
        while ((par = par.parentNode).subContainers) {
            if (!par.subContainers[1]) continue;
            var overlap = getOverlap(par);
            //log("comparing subcontainers for overlap: " + par.str);
            if (overlap) {
                log(overlap+" overlap between "+par.subContainers[0].str+" and "+par.subContainers[1].str);
                var x1 = parseInt(par.subContainers[0].style.left) - Math.ceil(overlap/2);
                var x2 = parseInt(par.subContainers[1].style.left) + Math.ceil(overlap/2);
                par.subContainers[0].style.left = x1 + "px";
                par.subContainers[1].style.left = x2 + "px";
                if (par.pixels) for (var i=0; i<par.pixels.length; i++) freePixels.push(par.removeChild(par.pixels[i]));
                var line1 = this.drawLine(par, 0, par.h, x1, par.h + this.branchingHeight);
                var line2 = this.drawLine(par, 0, par.h, x2, par.h + this.branchingHeight);
                par.pixels = line1.concat(line2);
                // now that sub0 has been moved left, it may itself overlap something, so we continue the loop
            }
        }
        // get absolute x-position of leftmost container (relative to rootAnchor):
        var minX = 0;
        var con, cons = [this.rootAnchor.firstChild];
        while ((con = cons.shift())) {
            con.__x = (con.parentNode.__x || 0) + parseInt(con.style.left);
            if (con.__x - con.w < minX) minX = con.__x - con.w/2;
            cons = cons.concat(con.subContainers);
        }
        if (minX < this.minX) {
            log("minX " + minX + ": tree out of left document border by " + (this.minX - minX));
            this.rootAnchor.firstChild.style.left = this.rootAnchor.firstChild.__x + (this.minX - minX) + "px";
        }
    }
    
    this.highlight = function(children, parent) {
        while (highlighted.length) highlighted.shift().div.className = this.nodeCSS;
        for (var i=0; i<children.length; i++) children[i].div.className = this.nodeHiChildCSS;
        highlighted = children.copy();
        if (parent) {
            parent.div.className = this.nodeHiParentCSS;
            highlighted.push(parent);
        }
    }
    
    this.drawLine = function(el, x1, y1, x2, y2) {
        var distX = x2 - x1;
        var distY = y2 - y1;
        var dist = Math.sqrt(distX*distX + distY*distY);
        var pxX = distX/dist;
        var pxY = distY/dist;
        var drawn = 1;
        var dotX = x1;
        var dotY = y1;
        var pixels = [];
        while (drawn < dist) {
            if ((dotX != Math.round(x1 + drawn*pxX) || dotY != Math.round(y1 + drawn*pxY)) && (drawn % this.pixelDistanceOnLine == 0)) {
                dotX = Math.round(x1 + drawn*pxX);
                dotY = Math.round(y1 + drawn*pxY);
                if (freePixels.length > 0) {
                    var pixel = freePixels.shift();
                    el.appendChild(pixel);
                }
                else {
                    var pixel = document.createElement("div");
                    el.appendChild(pixel);
                    pixel.style.position = "absolute";
                    pixel.style.width = "1px";
                    pixel.style.height = "1px";
                    pixel.style.clip = "rect(0 1px 1px 0)";
                    pixel.style.backgroundColor = this.lineColor;
                }
                pixel.style.left = dotX + "px";
                pixel.style.top = dotY + "px";
                pixels.push(pixel);
            }
            drawn++;
        }
        return pixels;
    }
    
    function getNextUnpainted(tree) {
        var nodes = [tree.nodes[0]];
        var node;
        while ((node = nodes.shift())) {
            do {
                if (!node.div) return node;
                if (node.children.length == 2) nodes.unshift(node.children[1]);
            } while ((node = node.children[0]));
        }
        return null;
    }
    
    function getOverlap(par) {
        var overlap = 0;
        // compare all pairs of sub(sub...)Containers:
        var co1, co2, co1s = [par.subContainers[0]], co2s;
        par.__x = 0; par.__y = 0;
        while ((co1 = co1s.shift())) {
            co2s = [par.subContainers[1]];
            while ((co2 = co2s.shift())) {
                co1.__x = co1.parentNode.__x + parseInt(co1.style.left);// - co1.w/2; // containers are all dots in the center of the column
                co1.__y = co1.parentNode.__y + parseInt(co1.style.top);
                co2.__x = co2.parentNode.__x + parseInt(co2.style.left);// - co2.w/2;
                co2.__y = co2.parentNode.__y + parseInt(co2.style.top);
                //debug("co1 "+co1.str+" x "+co1.__x+", y "+co1.__y+", w "+co1.w+", h "+co1.h);
                //debug("co2 "+co2.str+" x "+co2.__x+", y "+co2.__y+", w "+co2.w+", h "+co2.h);
                if ((co1.__y >= co2.__y) && (co1.__y < co2.__y + co2.h) || (co2.__y >= co1.__y) && (co2.__y < co1.__y + co1.h)) { // y-overlap > 0
                    var overlap12 = (co1.__x + co1.w/2 + painter.branchPadding) - (co2.__x - co2.w/2);
                    overlap = Math.max(overlap, overlap12);
                    // debug(overlap12);
                }
                co2s = co2s.concat(co2.subContainers);
            }
            co1s = co1s.concat(co1.subContainers);
        }
        return Math.floor(overlap);
    }
    
}
