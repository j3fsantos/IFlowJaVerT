/**
	@pred isNil (l) :
		l == {{ }};
	
	@pred isHole(l, alpha) :
		l == {{ "hole", alpha }};
	
	@pred isText(l, id, txt) :
		l == {{ "text", id, txt }};
	
	@pred isElement(l, name, id, l_attr, l_child) :
		l == {{ "elem", name, id, l_attr, l_child }};
	
	@pred isAttr(l, name, id, l_tf) :
		(l == {{ "attr", name, id, l_tf }});

	@pred DOMObject(l, proto) :
		types (l : $$object_type) *
		((l, "@proto") -> proto) *
		((l, "@class") -> "Object") *
		((l, "@extensible") -> $$f);

	@pred DOMField(l, prop, v) :
		dataFieldConst(l, prop, v);

	@pred DOMFunctionObject(l, call) :
		types(l : $$object_type, call : $$string_type) *
		((l, "@proto") -> $lfun_proto) *
		((l, "@class") -> "Function") *
		((l, "@extensible") -> $$f) *
		((l, "@scope") -> {{ $lg }}) *
		((l, "@call")  -> call) *
		empty_fields(l : "@scope", "@call");
	
	@pred DOMFunctionField(l, call) :
		DOMField(l, call, #lnn) *
		DOMFunctionObject(#lnn, call);

	@pred NodePrototype() :
		DOMObject($l_np, $$null) *
		DOMFunctionField($l_np, "nodeName") *
		DOMFunctionField($l_np, "nodeValue") *
		DOMFunctionField($l_np, "nodeType") *
		DOMFunctionField($l_np, "parentNode") *
		DOMFunctionField($l_np, "childNodes") *
		DOMFunctionField($l_np, "firstChild") *
		DOMFunctionField($l_np, "lastChild") *
		DOMFunctionField($l_np, "previousSibling") *
		DOMFunctionField($l_np, "nextSibling") *
		DOMFunctionField($l_np, "ownerDocument") *
		DOMFunctionField($l_np, "insertBefore") *
		DOMFunctionField($l_np, "replaceChild") *
		DOMFunctionField($l_np, "removeChild") *
		DOMFunctionField($l_np, "appendChild") *
		DOMFunctionField($l_np, "hasChildNodes") *
		empty_fields($l_np : "nodeName", "nodeValue", "nodeType", "parentNode", "childNodes", "firstChild",
			"lastChild", "previousSibling", "nextSibling", "ownerDocument", "insertBefore", "replaceChild", "removeChild", "appendChild", "hasChildNodes");

	@pred DocumentNodePrototype() :
		DOMObject($l_dnp, $l_np) *
		DOMFunctionField($l_dnp, "documentElement") *
		DOMFunctionField($l_dnp, "createElement") *
		DOMFunctionField($l_dnp, "createTextNode") *
		DOMFunctionField($l_dnp, "createAttribute") *
		DOMFunctionField($l_dnp, "getElementsByTagName") *
		empty_fields($l_dnp : "documentElement", "createElement", "createTextNode", "createAttribute", "getElementsByTagName");

	@pred DocumentNode(dn, l_element, element, l_grove, grove) :
		DOMObject(dn, $l_dnp) *
		((dn, "@element") -> l_element) * DocumentElement(l_element, element) *
		((dn, "@grove") -> l_grove) * Grove(l_grove, grove) *
		empty_fields(dn : "@element", "@grove");

	@pred ElementNodePrototype() :
		DOMObject($l_enp, $l_np) *
		DOMFunctionField($l_enp, "tagName") *
		DOMFunctionField($l_enp, "getAttribute") *
		DOMFunctionField($l_enp, "setAttribute") *
		DOMFunctionField($l_enp, "removeAttribute") *
		DOMFunctionField($l_enp, "getAttributeNode") *
		DOMFunctionField($l_enp, "setAttributeNode") *
		DOMFunctionField($l_enp, "removeAttributeNode") *
		DOMFunctionField($l_enp, "getElementsByTagName") *
		empty_fields($l_enp : "tagName", "getAttribute", "setAttribute", "removeAttribute", "getAttributeNode",
			"setAttributeNode", "removeAttributeNode", "getElementsByTagName");

	@pred ElementNode(name, en, l_attr, attr, l_children, children) :
		DOMObject(en, $l_enp) *
		((en, "@name") -> name) *
		((en, "@attributes") -> l_attr) * AttributeSet(l_attr, attr) *
		((en, "@children") -> l_children) * Forest(l_children, children) *
		empty_fields(en : "@name", "@attributes", "@children");

	@pred TextNodePrototype() :
		DOMObject($l_tnp, $l_np) *
		DOMFunctionField($l_tnp, "data") *
		DOMFunctionField($l_tnp, "length") *
		DOMFunctionField($l_tnp, "substringData") *
		DOMFunctionField($l_tnp, "appendData") *
		DOMFunctionField($l_tnp, "insertData") *
		DOMFunctionField($l_tnp, "deleteData") *
		DOMFunctionField($l_tnp, "replaceData") *
		DOMFunctionField($l_tnp, "splitText") *
		empty_fields($l_tnp : "data", "length", "substringData", "appendData",
								"insertData", "deleteData", "replaceData", "splitText");

	@pred TextNode(tn, text) :
		DOMObject(tn, $l_tnp) *
		((tn, "@text") -> text) *
		empty_fields(tn : "@text");

	@pred AttributeNodePrototype() :
		DOMObject($l_anp, $l_np) *
		empty_fields($l_anp :);

	@pred AttributeNode(name, an, l_textforest, textforest) :
		DOMObject(an, $l_anp) *
		((an, "@name") -> name) *
		((an, "@textforest") -> l_textforest) * TextForest(l_textforest, textforest) *
		empty_fields(an : "@name", "@textforest");


	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();

		
	@pred DocumentElement(l, element) :
		(element == {{ }}) * ((l, "@next") -> $$null) * empty_fields(l : "@next"),

		(element == {{ "elem", #id, #name, #l_a, #l_c }}) * isElement(element, #id, #name, #l_a, #l_c) * 
		((l, "@next") -> $$null) * empty_fields(l : "@next"),

		isHole(element, #alpha) * ((l, "@next") -> $$null) * empty_fields(l : "@next");

	@pred AttributeSet(l, attrs) : 
		isNil(attrs) * ((l, "@next") ->  $$null) * empty_fields(l: "@next"),
		
		(attrs == (#head :: #attrsNext)) * isAttr(#head, #name, #id, #l_tf) * 
		((l, "@next") -> #next) * AttributeSet(#next, #attrsNext) * empty_fields(l : "@next"); 	

	@pred Forest(l, childList) :
		isNil(childList) * ((l, "@next") ->  $$null) * empty_fields(l: "@next"),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) *
		((l, "@next") -> #next) * Forest(#next, #childListNext) * empty_fields(l : "@next"),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #l_a, #l_c) *
		((l, "@next") -> #next) * Forest(#next, #childListNext) * empty_fields(l : "@next"),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		((l, "@next") -> #next) * Forest(#next, #childListNext) * empty_fields(l : "@next");

	
	@pred TextForest(l, childList) :
		isNil(childList) * ((l, "@next") ->  $$null) * empty_fields(l: "@next"),

		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) *
		((l, "@next") -> #next) * TextForest(#next, #childListNext) * empty_fields(l : "@next"),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		((l, "@next") -> #next) * TextForest(#next, #childListNext) * empty_fields(l : "@next");
	
	@pred Grove(l, content) :
		isNil(content) * ((l, "@next") ->  $$null) * empty_fields(l: "@next"),
		
		(content == (#head :: #contentNext)) * isText(#head, #id, #text) *
		((l, "@next") -> #next) * Grove(#next, contentNext) * empty_fields(l : "@next"),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #l_a, #l_c) *
		((l, "@next") -> #next) * Grove(#next, #contentNext) * empty_fields(l : "@next"),
		
		(content == (#head :: #contentNext)) * isAttr(head, #name, #id, #l_tf) *
		((l, "@next") -> #next) * Grove(#next, #contentNext) * empty_fields(l : "@next"),
			
		(content == (#head :: #contentNext)) * isHole(#head, #alpha) *
		((l, "@next") -> #next) * Grove(#next, #contentNext) * empty_fields(l : "@next");

	@pred Cell(l, ctx, content) :
		isNil(content) * ((l, "@context") -> ctx) * ((l, "@next") ->  $$null) * empty_fields(l: "@context", "@next"),
		
		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * ((l, "@context") -> ctx) *
		((l, "@next") -> #next) * Cell(#next, contentNext) * empty_fields(l : "@context", "@next"),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #l_a, #l_c) * ((l, "@context") -> ctx) *
		((l, "@next") -> #next) * Cell(#next, #contentNext) * empty_fields(l : "@context", "@next"),
		
		(content == (#head :: #contentNext)) * isAttr(head, #name, #id, #l_tf) * ((l, "@context") -> ctx) *
		((l, "@next") -> #next) * Cell(#next, #contentNext) * empty_fields(l : "@context", "@next"),
			
		(content == (#head :: #contentNext)) * isHole(#head, #alpha) * ((l, "@context") -> ctx) *
		((l, "@next") -> #next) * Cell(#next, #contentNext) * empty_fields(l : "@context", "@next");


	@pred val(t, s) :
		isNil(t) * (s == ""),
		(t == (#head :: #childListNext)) * isText(#head, #id, #s1) * val(#childListNext, #s2) * (s == #s1 ++ #s2);

	@pred out(a, s) :
		isNil(a),
		(a == (#head :: #childListNext)) * isAttr(#head, #name, #id, #l_tf) * (! (s == #name)) * 
		out(#childListNext, s) * types(s: $$string_type, #name: $$string_type);

	@pred complete(l) :
		isNil(l),
		(l == (#head :: #next)) * isText(#head, #id, #s1) * complete(#next),
		(l == (#head :: #next)) * isAttr(#head, #n, #id, #l_tf) * complete(#next),
		(l == (#head :: #next)) * isElement(#head, #n, #id, #l_a, #l_c) * complete(#next);

	@pred GroveCell(l) :
		Cell(l, "grove", #any);

	@pred GroveOrForestCell(lh) :
		Cell(l, "grove", #any),
		Cell(l, "forest", #any);


	@onlyspec allocG(l, i, j)
		pre:  [[ (l == #l) * (i == #i) * (j == #j) * types(#g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ (#g2 @ #g3)) * (l-len(#g1) == #i) * (l-len(#g2) == #j) ]]
		post: [[ Grove(#l, (#g1 @ ({{ "hole", #alpha }} :: #g3))) * Cell(#alpha, "grove", #g2) * (ret == #alpha) * types(#alpha : $$object_type) ]]
		outcome: normal;

		pre:  [[ (l == #l) * (i == 0) * (j == 0) * types(#g : $$list_type) * Grove(#l, #g) ]]
		post: [[ Grove(#l, ({{ "hole", #alpha }} :: #g)) * Cell(#alpha, "grove", {{ }}) * (ret == #alpha) ]]
		outcome: normal

	@onlyspec deallocG(alpha)
		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g3)) * Cell(#alpha, "grove", #g2) ]]
		post: [[ Grove(#l, (#g1 @ (#g2 @ #g3))) ]]
		outcome: normal

*/ /*
	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * Cell(#l, #any, {{ {{ "elem", #name, this, #l_attr, #l_c }} }}) * ElementNode(#name, this, #l_attr, #attr, #l_c, #c) *
				 (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * val(#t, #s1) * types(#s1 : $$string_type) ]]
		post: [[ (s == #s) * Cell(#l, #any, {{ {{ "elem", #name, this, #l_attr, #l_c }} }}) * ElementNode(#name, this, #l_attr, #attr, #l_c, #c) *
				 (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * (ret == #s1) ]]
		outcome: normal;
		
		pre:  [[ (s == #s) * Cell(#l, #any, {{ {{ "elem", #name, this, #l_attr, #l_c }} }}) * 
				 ElementNode(#name, this, #l_attr, #attr, #l_c, #c) * out(#attr, #s) ]]
		post: [[ (s == #s) * Cell(#l, #any, {{ {{ "elem", #name, this, #l_attr, #l_c }} }}) * 
				 ElementNode(#name, this, #l_attr, #attr, #l_c, #c) * (ret == "")    ]]
		outcome: normal

	@onlyspec setAttribute(s, v)
		pre:  [[ Cell(#l, #ctx1, {{ {{ "elem", #name, this, #l_attr, #l_c }} }}) * ElementNode(#name, this, #l_attr, #attr, #l_c, #c) *
				 (#attr == {{ {{ "attr", #s1, #m, #l_tf }}, {{ "hole", #alpha }} }}) * AttributeNode(#s1, #m, #l_tf, #tf) *
				 Cell(#l_g, "grove", {{ }}) * (s == #s1) * (v == #s2) ]]
		post: [[ Cell(#l, #ctx1, {{ {{ "elem", #name, this, #l_attr, #l_c }} }}) * ElementNode(#name, this, #l_attr, #attr, #l_c, #c) *
				 (#attr_post == {{ {{ "attr", #s1, #m, #l_tf_post }}, {{ "hole", #alpha }} }}) * AttributeNode(#s1, #m, #l_tf, #tf_post) * 
				 (#tf_post == {{ {{ "text", #r, #s2 }} }}) * Cell(#l_g, "grove", #tf) ]]
		outcome: normal;

		pre:  [[ Cell(#l, #ctx1, {{ {{ "elem", #name, this, #l_attr, #l_c }} }}) * ElementNode(#name, this, #l_attr, #attr, #l_c, #c) * 
				 (s == #s1) * (v == #s2) * out(#attr, #s1) ]]
		post: [[ Cell(#l, {{ #ctx1, {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(#name, this, #l_attr, #attr_post, #l_c, #c) * 
				 (#attr_post == {{ "attr", #s1, #m, #l_tf }} :: #attr) * AttributeNode(#s1, #m, #l_tf, #tf) * (#tf == {{ {{ "text", #r, #s2 }} }}) ]]
		outcome: normal

	@onlyspec ownerDocument()
		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_c, #c) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_c, #c) * (ret == $l_document) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #t) ]]
		post: [[ TextNode(this, #t) * (ret == $l_document) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#s1, this, #l_tf, #tf) ]]
		post: [[ AttributeNode(#s1, this, #l_tf, #tf) * (ret == $l_document) ]]
		outcome: normal

	@onlyspec createElement(s)
		pre:  [[ (s == #name) *  DocumentNode(this, #l_element, #element, #l_g, #g) ]]
		post: [[ (ret == #en) * DocumentNode(this, #l_element, #element, #l_g, ({{ {{ "elem", #name, #en, #e_l_a, #e_l_c }} }} @ #g)) * 
				 ElementNode(#name, #en, #e_l_a, {{ }}, #e_l_c, {{ }}) ]]
		outcome: normal

	@onlyspec appendChild(n)
		pre:  [[ (n == #n) * Cell(#l, #ctx1, {{ {{ "elem", #e_n, this, #l_ea, #l_ec }} }}) * 
				 ElementNode(#e_n, this, #l_ea, #ea, #l_ec, #ec) * (#ec == {{ {{ "hole", #gamma }} }}) *
				 Cell(#alpha, #ctx2, #g) * (#g == {{ {{ "elem", #e_n2, #n, #e_l_a2, #e_l_c2 }} }}) *
				 ElementNode(#e_n2, #n, #e_l_a2, #e_a2, #e_l_c2, #e_c2) * complete(#e_c2) ]]
		post: [[ Cell(#l, #ctx1, {{ {{ "elem", #e_n, this, #l_ea, #l_ec }} }}) * 
				 ElementNode(#e_n, this, #l_ea, #ea, #l_ec, #ec_post) * 
				 (#ec_post == {{ {{ "hole", #gamma }}, {{ "elem", #e_n2, #n, #e_l_a2, #e_l_c2 }} }}) *
				 Cell(#alpha, #ctx2, {{ }}) * ElementNode(#e_n2, #n, #e_l_a2, #e_a2, #e_l_c2, #e_c2) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (n == #n) * Cell(#l, #ctx1, {{ {{ "elem", #e_n, this, #l_ea, #l_ec }} }}) * 
				 ElementNode(#e_n, this, #l_ea, #ea, #l_ec, #ec) * (#ec == {{ {{ "hole", #gamma }} }}) *
				 Cell(#alpha, #ctx2, #g) * (#g == {{ {{ "text", #n, #t2 }} }}) * TextNode(#n, #t2) ]]
		post: [[ Cell(#l, #ctx1, {{ {{ "elem", #e_n, this, #l_ea, #l_ec }} }}) * 
				 ElementNode(#e_n, this, #l_ea, #ea, #l_ec, #ec_post) * (#ec_post == {{ {{ "hole", #gamma }}, {{ "text", #n, #t2 }} }}) * 
				 Cell(#alpha, #ctx2, {{ }}) * TextNode(#n, #t2) * (ret == #n) ]]
		outcome: normal

*/

/**
	@id createNewAttribute
	@rec false

	@pre (
		scope(allocG   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocG : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() * (element == #en) * (grove == #d_g) * types(#en : $$object_type, #e_a: $$list_type, #e_c: $$list_type) *
		Cell(#r, #ctx_e, {{ {{ "elem", #name, #en, #e_l_a, #e_l_c }} }}) * 
		ElementNode(#name, #en, #e_l_a, #e_a, #e_l_c, #e_c) *
		(#e_c == {{ {{ "hole", #alpha }} }}) *
		DocumentNode($l_document, #d_l_elem, #d_elem, #d_l_g, #d_g) *
		(#d_g == {{ {{ "hole", #beta }} }})
	)
	@post (
		scope(allocG   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocG : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() * (ret == $$t) * 
		Cell(#r, #ctx_e, {{ {{ "elem", #name, #en, #e_l_a, #e_l_c }} }}) * 
		ElementNode(#name, #en, #e_l_a, #e_a, #e_l_c, #e_c_post) *
		(#e_c_post == {{ {{ "hole", #alpha }}, {{ "elem", #e_n_new, #e_new, #e_attr_new, #e_chld_new }} }}) *
		ElementNode(#e_n_new, #e_new, #e_attr_new, $$nil, #e_chld_new, $$nil) * 
		DocumentNode($l_document, #d_l_elem, #d_elem, #d_l_g, #d_g_post) *
		(#d_g_post == {{ {{ "hole", #beta }} }})
	)
*/
function createNewAttribute(grove, element){
	var d = element.ownerDocument();
	var e = d.createElement("test");
	var a = allocG(grove, 0, 1);
	/* @invariant 
		scope(e : #e2) * 
		ElementNode(#name2, #e2, #e_l_a2, #e_a2, #e_l_c2, #e_c2) */
	/* @fold complete(#e_c2) */
	var n = element.appendChild(e);
	deallocG(a);
	return (n === e);
}