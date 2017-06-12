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

function secondChild(element) {
	var r = element.firstChild();
	var s = r.nextSibling();
	return s;
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
	if (isNavigatorIE()) {
		var msViewportStyle = document.createElement('style');
		var t = document.createTextNode(
				"@-ms-viewport{width:auto!important}"
			);
		msViewportStyle.appendChild(t);
		document.appendChild(msViewportStyle);
	}
}

/** 
	@toprequires (DocumentNode($l_document, #l_element, {{ }}, {{ }}) * InitialDOMHeap() * scope(document : $l_document))
	@topensures  (DocumentNode($l_document, #l_element, {{ }}, {{ {{ "elem", "one", #ret, {{ }}, {{ }} }} }}) * InitialDOMHeap() * scope(document : $l_document))
*/
document.createElement("one");

/** 
-------------------------------------------------------------------------------
		preallocated cell encoding -- prealloc_DOM.js
-------------------------------------------------------------------------------
**/

/**
	@id isSquare

	@pre (
		InitialDOMHeap() * (element == #enx) *
		ECell(#alpha, #name, #enx, #l_aList, #aList, #l_cList, #cList) *
		(#aList == #a1 @ {{ {{ "hole", #beta1 }} }} @ #a2 @ {{ {{ "hole", #beta2 }} }} @ #a3) *
		ACell(#beta1, "width", #an1, #l_aa1, #aa1) * ACell(#beta2, "height", #an2, #l_aa2, #aa2) *
		val(#aa1, #s1) * val(#aa2, #s1) * types(#s1 : $$string_type, #s2 : $$string_type)
	)
	@post (
		InitialDOMHeap() * (ret == $$t) *
		ECell(#alpha, #name, #enx, #l_aList, #aList, #l_cList, #cList) *
		ACell(#beta1, "width", #an1, #l_aa1, #aa1) * ACell(#beta2, "height", #an2, #l_aa2, #aa2) *
		val(#aa1, #s1) * val(#aa2, #s1)
	)
*/
function isSquare(element) {
	var w = element.getAttribute("width");
	var y = element.getAttribute("height");
	return w === y;
}

/**
	@id childToParent

	@pre (
		InitialDOMHeap() * scope(document : $l_document) *
		(element == #enx) *
		ECell(#alpha, #name, #enx, #l_aList, #aList, #l_cList, #cList) *
		(#cList == {{ "hole", #beta }} :: #a1) *
		ECell(#beta, #name2, #enx2, #l_aList2, #aList2, #l_cList2, #cList2)
	)
	@post (
		InitialDOMHeap() * scope(document : $l_document) *
		ECell(#alpha, #name, #enx, #l_aList, #aList, #l_cList, #cList) *
		ECell(#beta, #name2, #enx2, #l_aList2, #aList2, #l_cList2, #cList2) * (ret == #enx)
	)
*/
function childToParent(element) {
	var c = element.firstChild();
	var p = c.parentNode();
	return p;
}

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
	@id secondChild
	@pre (
		InitialDOMHeap() * scope(document : $l_document) *
		(element == #enx1) *
		ECell(#alpha, #name, #enx1, #l_aList, #aList, #l_cList, #cList) *
		(#cList == {{ {{ "hole", #beta }}, {{ "hole", #gamma }} }} @ #a1) *
		ECell(#beta,  #name2, #enx2, #l_aList2, #aList2, #l_cList2, #cList2) *
		ECell(#gamma, #name3, #enx3, #l_aList3, #aList3, #l_cList3, #cList3)
	)
	@post (
		InitialDOMHeap() * scope(document : $l_document) *
		ECell(#alpha, #name, #enx1, #l_aList, #aList, #l_cList, #cList) *
		ECell(#beta,  #name2, #enx2, #l_aList2, #aList2, #l_cList2, #cList2) *
		ECell(#gamma, #name3, #enx3, #l_aList3, #aList3, #l_cList3, #cList3) *
		(ret == #enx3)
	)
*/
function secondChild(element) {
	var r = element.firstChild();
	/* @unfold ElementNode(#name, #enx1, #l_aList, #aList, #l_cList, #cList) */
	var s = r.nextSibling();
	/* @fold ElementNode(#name, #enx1, #l_aList, #aList, #l_cList, #cList) */
	return s;
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

/* 
-- BootStrap example Specifics --
*/ /*
	@pred isIE() :    (this == #this) * isIE();
	@pred notisIE() : (this == #this) * notisIE();

	@onlyspec isNavigatorIE()
		pre:  [[ isIE() ]]
		post: [[ isIE() * (ret == $$t) ]]
		outcome: normal;
		pre:  [[ notisIE() ]]
		post: [[ notisIE() * (ret == $$f) ]]
		outcome: normal
*/

/*  Bootstrap IE10 viewport bug workaround.
	Slightly modified from source: Pulled a nested call out and replaced some inaccessible functions.
	From: https://github.com/twbs/bootstrap/blob/master/docs/assets/js/ie10-viewport-bug-workaround.js
*/

/**
	@id viewportBug

	@pre (
		scope(isNavigatorIE: #isnav_fun) * fun_obj(isNavigatorIE, #isnav_fun, #isnav_proto) *
		InitialDOMHeap() * scope(document: $l_document) * isIE() *
		DocumentNode($l_document, #l_elem, {{ }}, #d_l_g, #d_g)
	)
	@post (
		InitialDOMHeap() * isIE() *
		DocumentNode($l_document, #l_elem, {{ {{ "hole", #alpha }} }}, #d_l_g, #d_g) *
		ECell(#alpha, "style", #enx, #enx_l_a, {{}}, #enx_l_cList, {{ {{ "hole", #beta }} }}) *
		TCell(#beta, #tid, "@-ms-viewport{width:auto!important}")
	)
*/
function ie10viewportbugworkaround() {
	if (isNavigatorIE()) {
		var msViewportStyle = document.createElement('style');
		var t = document.createTextNode("@-ms-viewport{width:auto!important}");
		msViewportStyle.appendChild(t);
		document.appendChild(msViewportStyle);
		/* @invariant Grove(#d_l_g, #list) * (#list == ({{ "hole", #a }} :: ({{ "hole", #b }} :: #d_g))) */
		/* @callspec deallocG(#any1, #d_l_g, #a) */
		/* @callspec deallocG(#any1, #d_l_g, #b) */
		return;
	}
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
		InitialDOMHeap() *
		(img == #n) * (cat == #s2) * 
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children) *
		out(#attr, "src")
	)
	@post (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		InitialDOMHeap() *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children)
	)	
	@pre (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 1) * standardObject(#c) * 
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
	@pre (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 0) * standardObject(#c) * 
		InitialDOMHeap() *
		(img == #n) * (cat == #s2) * 
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children) *
		(#attr == #a1 @ ({{ "hole", #gamma }} :: #a2)) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * nisB(#s1) * isNamedProperty(#s1) * 
		Grove(#grove, {{}})
	)
	@post (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		scope(cache: #c) * dataField(#c, #s1, 0) * standardObject(#c) * 
		InitialDOMHeap() *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * nisB(#s1) * Grove(#grove, {{}})
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

	@pred safeName(s) :
		(s == #c ++ #s2) * types(#c: $$string_type, #s2: $$string_type) * (s-len(#c) == 1) * (! (#c == "#")) * safeName(#s2);

*/