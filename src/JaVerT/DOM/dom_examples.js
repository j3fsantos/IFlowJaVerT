/**
	Functions to verify that may lead to interesting specs and limitations.
*/

function isSquare(element) {
	var w = element.getAttribute("width");
	var y = element.getAttribute("height");
	return w === y;
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
-------------------------------------------------------------------------------
		cell encoding -- new_DOM.js
-------------------------------------------------------------------------------
**/

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
		(#d_g_post == {{ "text", #tid, #text }} :: #d_g) *
		(ret == $$null)
	)
*/
function groveParent(s) {
	var t = document.createTextNode(s);
	/* @flash GroveRec(#d_l_g, #any, (#t1 :: #d_g)) */
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
	@id createNewAttribute
	@rec false

	@pre (
		InitialDOMHeap() * (element == #id) * types(#en : $$object_type) *
		DocumentNode($l_document, #l_elem, #elem, #l_gList, #gList) *
		ECell(#alpha, #name, #id, #l_aList1, #aList1, #l_cList1, #cList1)
	)
	@post (
		InitialDOMHeap() * (ret == $$t) * 
		DocumentNode($l_document, #l_elem, #d_elem, #d_l_g, #d_g_post) *
		ECell(#alpha, #name, #id, #l_aList1, #aList1, #l_cList1, #cList_post) *
		(#cList_post == (#cList1 @ {{ {{ "elem", "test", #n_id, #n_l_aList, #n_l_cList }} }}))
	)
*/
function createNewAttribute(element){
	var d = element.ownerDocument();
	var e = d.createElement("test");
	/* @callspec allocG(#zeta, #l_gList, 0) */
	0;
	
	/* @invariant scope(e : #e2) * ECell(#zeta, #name2, #e2, #l_aList2, #aList2, #l_cList2, #cList2) */
	/* @fold complete(#cList2) */
	var n = element.appendChild(e);
	/* @callspec deallocG(#whatever, #l_gList, #zeta) */
	return (n === e);
}

/**
	@id sanitise

	@pre (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 0) * standardObject(#c) * 
		InitialDOMHeap() *
		(img == #n) * (cat == #s2) * 
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children) *
		(#attr == a1 @ ({{ "attr", "src", #a, #tf1 }} :: a2)) *
		val(#tf1, #s1) * isB(#s1) * isNamedProperty(#s1) * 
		Grove(#grove, {{}})
	)
	@post (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 1) * standardObject(#c) * 
		InitialDOMHeap() *
		ECell(#alpha, #name, #n, #l_attr, #new_attr, #l_children, #children) *
		(#new_attr == a1 @ ({{ "attr", "src", #a, #tf2 }} :: a2)) *
		(#tf2 == {{ {{ "text", #r, #s2 }} }}) *
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


/** 
-------------------------------------------------------------------------------
		preallocated cell encoding -- prealloc_DOM.js
-------------------------------------------------------------------------------
**/

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

/**
	@id createNewAttribute
	@rec false

	@pre (
		InitialDOMHeap() * (element == #id) * types(#en : $$object_type) *
		DocumentNode($l_document, #l_elem, #elem, #l_gList, #gList) *
		ECell(#alpha, #name, #id, #l_aList1, #aList1, #l_cList1, #cList1)
	)
	@post (
		InitialDOMHeap() * (ret == $$t) * 
		DocumentNode($l_document, #l_elem, #elem, #l_gList, #gList) *
		ECell(#alpha, #name, #id, #l_aList1, #aList1, #l_cList1, #cList_post) *
		(#cList_post == (#cList1 @ {{ {{ "hole", #beta }} }})) *
		ECell(#beta, "test", #n_id, #n_l_aList, #n_aList, #n_l_cList, #n_cList)
	)
*/
function createNewAttribute(element){
	var d = element.ownerDocument();
	var e = d.createElement("test");
	/* @invariant scope(e : #e2) * ECell(#zeta, #name2, #e2, #l_aList2, #aList2, #l_cList2, #cList2) */
	/* @fold complete(#cList2) */
	var n = element.appendChild(e);
	/* @callspec deallocG(#nvm, #l_gList, #zeta) */
	return (n === e);
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
		(#attr == #a1 @ ({{ "hole", #gamma }} :: #a2)) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * isB(#s1) * isNamedProperty(#s1) * 
		Grove(#grove, {{}})
	)
	@post (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 1) * standardObject(#c) * 
		InitialDOMHeap() *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children) *
		(#attr == #a1 @ ({{ "hole", #gamma }} :: #a2)) *
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
	@id textAxioms

	@pre (
		InitialDOMHeap() * (tnode == #tn) *
		Forest(#f_loc, {{ {{ "hole", #alpha1 }} }}) *
		TCell(#alpha1, #tn, #text1_pre) * (#text1_pre == "abcdefghi")
	)
	@post (
		InitialDOMHeap() * (ret == 9) *
		Forest(#f_loc, {{ {{ "hole", #alpha1 }}, {{ "hole", #alpha2 }} }}) *
		TCell(#alpha1, #tn, #text1_post) * (#text1_post == "abcabcabc") *
		TCell(#alpha2, #tn2, #text2_post) * (#text2_post == "ghia")
	)
*/
function textAxioms(tnode) {
	var l = tnode.length();
	var c = tnode.substringData(0, 3);
	tnode.replaceData(3, 3, c);
	var t2 = tnode.splitText(6);
	t2.insertData(3, c);
	t2.deleteData(4, 10);
	tnode.appendData(c);
	return l
}

/*
-------------------------------------------------------------------------------
*/

/*
	Currently unsupported
	----Text Node predicates----
*/ /*
	
	@pred safeName(s) :
		(s == #c ++ #s2) * types(#c: $$string_type, #s2: $$string_type) * (s-len(#c) == 1) * (! (#c == "#")) * safeName(#s2);


*/