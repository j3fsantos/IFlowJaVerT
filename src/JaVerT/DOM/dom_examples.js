/**
	Functions to verify that may lead to interesting specs and limitations.
*/

function isSquare(element) {
	var w = element.getAttribute("width");
	var y = element.getAttribute("height");
	return w === y;
}

function createNewAttribute(element){
	var d = element.ownerDocument;
	var e = d.createElement("test");
	var n = element.appendChild(e);
	return n === e;
}