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

/**
	@id groveParent
	@rec false

	TODO: complete spec
	
	@pre (
		scope(allocAS   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocAS : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() *
		scope(document : $l_document) *
		DocumentNode($l_document, #l_element, #element, #grove)
	)
	@post (
		fun_obj(allocAS,   #allocAS,   #allocAS_proto) *
		fun_obj(deallocAS, #deallocAS, #deallocAS_proto) *
		InitialDOMHeap() *
		DocumentNode($l_document, #l_element, #element, ({{ "elem", "one", #ret, {{}}, {{}} }} :: #grove))
	)
*/
function groveParent(s) {
	var t = document.createTextNode(s);
	var r = t.parentNode();
	return r;
}

function childToParent(element) {
	var c = element.firstChild();
	var p = c.parentNode();
	return p;
}

function holePunch(element) {
	var r = element.firstChild();
	var s = r.nextSibling();
	return s;
}

/**
	@id singleGet
	@rec false

	@pre (
		scope(allocAS   : #allocAS)   * fun_obj(allocAS,   #allocAS,   #allocAS_proto) *
		scope(deallocAS : #deallocAS) * fun_obj(deallocAS, #deallocAS, #deallocAS_proto) *
		InitialDOMHeap() *
		(element == #en) * (l_attr == #l_attr) * types (#en : $$object_type, #l_attr : $$object_type) *
		ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) *
		(#attr == {{ 
			{{ "attr", "src", #a0, #atf0 }}, 
			{{ "attr", "width", #a1, #atf1 }}, 
			{{ "attr", "height", #a2, #atf2 }}, 
			{{ "hole", #a_alpha2 }} 
		}}) *
		(#atf0 == {{
			{{ "text", #t0, #s0 }},
			{{ "text", #t1, #s1 }}	
		}}
		)
	)
	
	@post (
		fun_obj(allocAS,   #allocAS,   #allocAS_proto) *
		fun_obj(deallocAS, #deallocAS, #deallocAS_proto) *
		InitialDOMHeap() *
		ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) *
		(ret == #s0 ++ #s1)
	)
*/
function singleGet(element, l_attr) {
	/* @unfold ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) */
	var a = allocAS(l_attr, 1, 3);
	/* @fold ElementNode(#name, #en, #l_attr, #attr_1, #l_children, #children) */ 
	/* @fold val(#atf0, #s) */
	var w = element.getAttribute("src");
	/* @unfold ElementNode(#name, #en, #l_attr, #attr_1, #l_children, #children) */
	deallocAS(a);
	/* @fold ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) */
	return w
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
	@toprequires (DocumentNode($l_document, #l_element, {{ }}, {{ }}) * InitialDOMHeap() * scope(document : $l_document))
	@topensures  (DocumentNode($l_document, #l_element, {{ }}, {{ {{ "elem", "one", #ret, {{ }}, {{ }} }} }}) * InitialDOMHeap() * scope(document : $l_document))
*/
document.createElement("one");

/*
	Currently unsupported
	----Text Node Axioms----
*/ /*
	
	@pred safeName(s) : 
	(!(s == #s1 ++ "#" ++ #s2));


	@onlyspec data()
		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == #text) * types(#text : $$string_type) ]]
		outcome: normal

	@onlyspec length()
		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == #l) * (#l == s-len(#text)) * types(#l : $$number_type) ]]
		outcome: normal

	@onlyspec substringData(o, c)
		pre:  [[ (o == #l1) * (c == #l2) * TextNode(this, #text) * (#text == #s1 ++ #s2 ++ #s3) * (#l1 == s-len(#s1)) * (#l2 == s-len(#s2)) * types(#text : $$string_type, #s1 : $$string_type, #s2 : $$string_type) ]]
		post: [[ TextNode(this, #text) * (ret == #s2) ]]
		outcome: normal;

		pre:  [[ (o == #l1) * (c == #l2) * TextNode(this, #text) * (#text == #s1 ++ #s2) (#l1 == s-len(#s1)) * (s-len(#s2) <=# #l2)  * types(#text : $$string_type, #s1 : $$string_type, #s2 : $$string_type)]]
		post: [[ TextNode(this, #text) * (ret == #s2) ]]
		outcome: normal

	@onlyspec appendData(s)
		pre:  [[ (s == #s2) * TextNode(this, #text) ]]
		post: [[ TextNode(this, (#text ++ #s2)) ]]
		outcome: normal

	@onlyspec insertData(o, s)
		pre:  [[ (o == #l1) * (s == #s3) * TextNode(this, (#s1 ++ #s2)) * (#l1 == s-len(#s1)) * types(#s1 : $$string_type, #s2 : $$string_type, #s3 : $$string_type) ]]
		post: [[ TextNode(this, (#s1 ++ #s3 ++ #s2)) ]]
		outcome: normal

	@onlyspec deleteData(o, c)
		pre:  [[ (o == #l1) * (c == #l2) * TextNode(this, (#s1 ++ #s2 ++ #s3)) * (#l1 == s-len(#s1)) * (#l2 == s-len(#s2)) * types(#s1 : $$string_type, #s2 : $$string_type, #s3 : $$string_type) ]]
		post: [[ TextNode(this, (#s1 ++ #s2)) ]]
		outcome: normal;

		pre:  [[ (o == #l1) * (c == #l2) * TextNode(this, (#s1 ++ #s2 ++ #s3)) * (#l1 == s-len(#s1)) * (s-len(#s2) <=# #l2) * types(#s1 : $$string_type, #s2 : $$string_type, #s3 : $$string_type) ]]
		post: [[ TextNode(this, #s1) ]]
		outcome: normal

	@onlyspec replaceData(o, c, s)
		pre:  [[ (o == #l1) * (c == #l2) * (s == #ns) * TextNode(this, (#s1 ++ #s ++ #s2)) * (#l1 == s-len(#s1)) * (#l2 == s-len(#s)) * types(#s1 : $$string_type, #s2 : $$string_type, #s : $$string_type, #ns : $$string_type) ]]
		post: [[ TextNode(this, (#s1 ++ #ns ++ #s2)) ]]
		outcome: normal

		pre:  [[ (o == #l1) * (c == #l2) * (s == #ns) * TextNode(this, (#s1 ++ #s)) * (#l1 == s-len(#s1)) * (s-len(#s) <=# #s) * types(#s1 : $$string_type, #s : $$string_type, #ns : $$string_type) ]]
		post: [[ TextNode(this, (#s1 ++ #ns)) ]]
		outcome: normal

	@onlyspec splitText(o)
		pre:  [[ (o == #l1) * Forest(#f, {{ {{ "text", this, (#s1 ++ #s2) }} }}) * (#l1 == s-len(#s1)) types(#s1 : $$string_type, #s2 : $$string_type) ]]
		post: [[ Forest(#f, {{ {{ this, #s1 }}, {{ "text", #n, #s2 }} }}) ]]
		outcome: normal

*/