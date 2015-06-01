
branchX = new Object(); // assoc. Array of the x-pos of all branches
branchX['0'] = 300;
branchY = new Object(); // the same with the y-pos of the _next_ node on the branch
branchY['0'] = 300;

nn4 = document.layers;
w3 = document.createElement;

function printNode(branch, fla, closed) {
	// calculate position:
	if (branchX[branch]) {
		var posX = branchX[branch];
		var posY = branchY[branch];
	}
	else {
		var parBranch = branch.substring(0,branch.length-1);
		var branchDir = branch.charAt(branch.length-1); // 0 = left, 1 = right
		var posY = branchY[branch] = branchY[parBranch];
		var posX = branchX[branch] = branchDir == 0 ? branchX[parBranch]-50 : branchX[parBranch]+50;
		// alert(posY+" - "+parBranch+" - "+branch);
	} 
	branchY[branch] += 20;
	
	// create Element:
	if (nn4) {
		el = new Layer(200,self);
		el.position = "absolute";
		el.top = posY;
		el.left = posX;
		el.visibility = "visible";
		el.document.write(fla);
		el.document.close();
	}
	else if (w3) {
		el = document.createElement("div");
		el.appendChild(document.createTextNode(fla));
		el.style.position = "absolute";
		el.style.top = posY;
		el.style.left = posX;
		document.body.appendChild(el);
	}
}
