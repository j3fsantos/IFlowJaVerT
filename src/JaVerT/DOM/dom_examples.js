/**
	Functions to verify that may lead to interesting specs and limitations.
*/

function isSquare(element) {
	var w = element.getAttribute("width");
	var y = element.getAttribute("height");
	return w === y;
}

/**
	@id createNewAttribute
	@rec false

	@pre (
		scope(allocG   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocG : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() * (element == #en) * (grove == #d_g) * types(#en : $$object_type) *
		ElementNode(#name, #en, #e_l_attr, #e_attr, #e_l_chld, #e_chld) *
		(#e_chld == {{ {{ "hole", #alpha }} }}) *
		DocumentNode($l_document, #d_l_elem, #d_elem, #d_l_g, #d_g) *
		(#d_g == {{ {{ "hole", #beta }} }})
	)
	@post (
		scope(allocG   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocG : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() * (ret == $$t) * 
		ElementNode(#name, #en, #e_l_attr, #e_attr, #e_l_chld, #e_chld_post) *
		(#e_chld_post == {{ {{ "hole", #alpha }}, {{ "elem", #e_n_new, #e_new, #e_attr_new, #e_chld_new }} }}) *
		DocumentNode($l_document, #d_l_elem, #d_elem, #d_l_g, #d_g) *
		(#d_g == {{ {{ "hole", #beta }} }}) * (ret == $$t)
	)
*/
function createNewAttribute(grove, element){
	/* @unfold ElementNode(#name, #en, #e_l_attr, #e_attr, #e_l_chld, #e_chld) */
	/* @fold ElementNode(#name, #en, #e_l_attr, #e_attr, #e_l_chld, #e_chld) */
	var d = element.ownerDocument();
	var e = d.createElement("test");
	var a = allocG(grove, 0, 1);
	/* @invariant scope(a : #zeta) * scope(e : #e) * Grove(#zeta, #g) * (#g == {{ {{ "elem", #name2, #e, #e_attr2, #e_chld2 }} }}) */
	/* @fold complete(#e_chld2) */
	/* @unfold ElementNode(#name, #en, #e_l_attr, #e_attr, #e_l_chld, #e_chld) */
	/* @fold ElementNode(#name, #en, #e_l_attr, #e_attr, #e_l_chld, #e_chld) */
	var n = element.appendChild(e);
	deallocG(a);
	return (n === e);
}
/* Still too much expansion from a basic function */
function createNewAttribute(element){
	var d = element.ownerDocument();
	var e = d.createElement("test");
	var n = element.appendChild(e);
	return (n === e);
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

function singleGet(element) {
	var w = element.getAttribute("src");
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

/** Bootstrap IE10 viewport bug workaround.
	Simple real life example, slightly modified: Removed an if condition and pulled a nested call out.
	From: https://github.com/twbs/bootstrap/blob/master/docs/assets/js/ie10-viewport-bug-workaround.js
*/
function ie10-viewport-bug-workaround() {
    var msViewportStyle = document.createElement('style');
    var t = document.createTextNode(
        "@-ms-viewport{width:auto!important}"
      );
    msViewportStyle.appendChild(t);
    document.appendChild(msViewportStyle);
}

/** 
	@toprequires (DocumentNode($l_document, #l_element, {{ }}, {{ }}) * InitialDOMHeap() * scope(document : $l_document))
	@topensures  (DocumentNode($l_document, #l_element, {{ }}, {{ {{ "elem", "one", #ret, {{ }}, {{ }} }} }}) * InitialDOMHeap() * scope(document : $l_document))
*/
document.createElement("one");

/**
	@id groveParent

	@pre (
		InitialDOMHeap() * scope(document : $l_document) *
		(s == #text) * types(#text: $$string_type) *
		DocumentNode($l_document, #l_elem, #d_elem, #d_l_g, #d_g)
	)
	@post (
		InitialDOMHeap() * scope(document : $l_document) *
		DocumentNode($l_document, #l_elem, #d_elem, #d_l_g, #d_g_post) *
		(#d_g_post == {{ "hole", #someAddress }} :: #d_g) *
		TCell(#someAddress, #tid, #text) *
		(ret == $$null)
	)
*/
function groveParent(s) {
	var t = document.createTextNode(s);
	var r = t.parentNode();
	return r;
}

/** sanitiseImg specifics */
/**
	@pred isB(s) : (s == #s) * isB(s);
	@pred nisB(s) : (s == #s) * nisB(s);

	@onlyspec isBlackListed(s)
		pre:  [[ (s == #s) * isB(#s) ]]
		post: [[ isB(#s) * (ret == 1) ]]
		outcome: normal;
		pre:  [[ (s == #s) * (nisB(#s)) ]]
		post: [[ (ret == 0) * (nisB(#s)) ]]
		outcome: normal
*/

/**
	@id sanitise

	@pre (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 0) * standardObject(#c) * 
		InitialDOMHeap() *
		(img == #n) * (cat == #s2) * 
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children) *
		(#attr == {{ {{ "hole", #alpha1 }}, {{ "hole", #gamma }}, {{ "hole", #alpha2 }} }}) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * isB(#s1) * isNamedProperty(#s1) * 
		Grove(#grove, {{}})
	)
	@post (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 1) * standardObject(#c) * 
		InitialDOMHeap() *
		ECell(#alpha, #name, #n, #l_attr, #new_attr, #l_children, #children) *
		(#new_attr == {{ {{ "hole", #alpha1 }}, {{ "hole", #gamma }}, {{ "hole", #alpha2 }} }}) *
		ACell(#gamma, "src", #a, #l_tf, #tf2) *
		(#tf2 == {{ {{ "hole", #gamma2 }} }}) *
		TCell(#gamma2, #r, #s2) *
		isB(#s1) *
		Grove(#grove, #tf1)
	)
**/
function sanitiseImg(img, cat){
	var url = img.getAttribute("src");
	if(url !== ""){
		var isB = cache[url];
		if(isB) {
			img.setAttribute("src", cat)
		} else {
			isB = isBlackListed(url);
			if(isB){
				img.setAttribute("src", cat);
				cache[url] = 1;
			}
		}
	}
}

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
		pre:  [[ (o == #l1) * (c == #l2) * TextNode(this, #text) * (#text == #s1 ++ #s2 ++ #s3) * (#l1 == s-len(#s1)) * (#l2 == s-len(#s2)) ]]
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