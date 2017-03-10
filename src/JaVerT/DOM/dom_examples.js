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

function builtSingleGet(element) {
	var t1 = document.createTextNode("test1");
	var t2 = document.createTextNode("test2");
	var a = document.createAttribute("src");
	a.appendChild(t1);
	a.appendChild(t2);
	element.setAttributeNode(a);
	var src = element.getAttribute("src");
	return src;
}

/**
Unsupported specs

	@pred safeName(s) : 
		(!(s == #s1 ++ "#" ++ #s2));

	@onlyspec setAttribute(s, v)
		pre:  [[ (s == #s1) * (v == #s2) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#attr == {{ {{ "attr", #s1, #m, #t }}, {{ "hole", #alpha }} }}) * Grove(#g_alpha, {{ }}) ]]
		post: [[ (s == #s1) * (v == #s2) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#attr == {{ {{ "attr", #s1, #m, #t2 }}, {{ "hole", #alpha }} }}) * (#t2 == {{ {{ "text", #r, #s2 }} }}) * Grove(#g_alpha, {{ #t }}) ]]
		outcome: normal;

		pre:  [[ (s == #s1) * (v == #s2) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * out(#attr, #s1) * safeName(#s2) ]]
		post: [[ (s == #s1) * (v == #s2) * ElementNode(#name, this, #l_attr, #attr2, #l_children, #children) * (#attr2 == {{ "attr", #s1, #m, #t }} :: #attr) * (#t == {{ {{ "text", #r, #s2 }} }}) ]]
		outcome: normal


*/