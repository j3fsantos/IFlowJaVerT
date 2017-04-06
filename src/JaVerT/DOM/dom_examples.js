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

/**
	@id singleGet
	@rec false

	@pre (
		InitialDOMHeap() * (element == #en) * types (#en : $$object_type) *
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
		InitialDOMHeap() * (ret == #s0 ++ #s1) *
		ElementNode(#name, #en, #l_attr, #attr, #l_children, #children)
	)
*/
function singleGet(element) {
	/* @unfold ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) */
	/* @callspec #a allocAS(#l_attr, 1, 3) */
	/* @fold ElementNode(#name, #en, #l_attr, #attr_1, #l_children, #children) */ 
	/* @fold val(#atf0, #s) */
	var w = element.getAttribute("src");
	/* @unfold ElementNode(#name, #en, #l_attr, #attr_1, #l_children, #children) */
	/* @callspec deallocAS(#a) */
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
	@id groveParent
	@rec false

	@pre (
		InitialDOMHeap() * (s == #s) * scope(document : $l_document) *
		types(#s : $$string_type, #grove: $$list_type) *
		DocumentNode($l_document, #l_element, #element, #l_grove, #grove) *
		(#grove == {{ {{ "hole", #alpha }} }})
	)
	@post (
		InitialDOMHeap() * scope(document : $l_document) * (ret == $$null) *
		types(#t : $$object_type) *
		DocumentNode($l_document, #l_element, #element, #l_grove, #grove) *
		(#grove == {{ {{ "text", #t, #s }}, {{ "hole", #alpha }} }})
	)
*/
/* 	Currently what we should end up with on our current direction. 
	Folds/unfolds of the grove are required to show that location #t is an object that has function ParentNode, 
		i.e. get to TextNode(#t, ...) which has TextNodePrototype which defines a function field parentNode.
	The amount of fold/unfold increases if we have to dig deeper into the structure.*/
function groveParent(s) {
	var t = document.createTextNode(s);
	/** @callspec #a allocG(#grove, 0, 0) */ /* Make the #grove list correspond to the spec of parentNode, with a context hole before and after the node. This is done here instead of after the fold/unfold just to demonstrate the use of invariant. To simplify things it should go just before parentNode call */
	/** @unfold Grove(#l_grove, #grove) */   /* Pull out the TextNode(t, ...) predicate that was implied after document.createTextNode(s) */
	/** @invariant ((#l_grove, "@next") -> #l_g2) */
	
	/** @unfold Grove(#l_g2, #g2) */
	/** @fold Grove(#l_g2, #g2) */
	/** @fold Grove(#l_grove, #grove) */     /* Undo the folds: we need the grove in list form for the parentNode spec */
	var r = t.parentNode();
	/** @callspec deallocG(#a) */            /* Undo internally required alloc */
	return r;
}

/* If we can create a macro that causes the fold/unfold cascade, the above simplifies and becomes more systematic */
function groveParent(s) {
	var t = document.createTextNode(s);
	/** @invariant (t == #t) */                      /* Register what has just been created. Maybe the variable and it's logical variable already exist and I missed that fact. */
	/** @callspec #a allocG(#grove, 0, 0) */         /* Make the #grove list correspond to the spec of parentNode, with a context hole before and after the node */
	/** @macro findNodePredicate(#t, #grove) */      /* Find the Node predicate associated to an address inside a 
	var r = t.parentNode();
	/** @callspec deallocG(#a) */
	return r;
}

/* If createTextNode introduces a "side effect" TextNode to whatever the tool has as state, we avoid fold/unfold of the grove. 
   What I mean here is maybe we can introduce a way to say, in the only specs, that TextNode(#t, ...) should be known to hold.
   We can't just add it to the post as it is a spatial predicate. */
function groveParent(s) {
	var t = document.createTextNode(s);
	/** @callspec #a allocG(#grove, 0, 0) */
	var r = t.parentNode();
	/** @callspec deallocG(#a) */
	return r;
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