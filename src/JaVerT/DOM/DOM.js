/**
	@pred isEmpty (l) :
		l == {{ }};
	
	@pred isHole(l, alpha) :
		l == {{ "hole", alpha }};
	
	@pred isText(l, id, txt) :
		l == {{ "text", id, txt }};
	
	@pred isElement(l, name, id, attrs, children) :
		l == {{ "elem", name, id, attrs, children }};
	
	@pred isAttr(l, name, id, tf) :
		l == {{ "attr", name, id, tf }};

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
		empty_fields(l : "@proto", "@class", "@extensible", "@scope", "@call");
	
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
		empty_fields($l_np : "@proto", "@class", "@extensible", "nodeName", "nodeValue", "nodeType", "parentNode", "childNodes", "firstChild",
			"lastChild", "previousSibling", "nextSibling", "ownerDocument", "insertBefore", "replaceChild", "removeChild", "appendChild", "hasChildNodes");

	@pred DocumentNodePrototype() :
		DOMObject($l_dnp, $l_np) *
		(($l_dnp, "@name") -> "#document") *
		DOMFunctionField($l_dnp, "documentElement") *
		DOMFunctionField($l_dnp, "createElement") *
		DOMFunctionField($l_dnp, "createTextNode") *
		DOMFunctionField($l_dnp, "createAttribute") *
		DOMFunctionField($l_dnp, "getElementsByTagName") *
		empty_fields($l_dnp : "@proto", "@class", "@extensible", "@name", "documentElement", "createElement", "createTextNode", "createAttribute", "getElementsByTagName");

	@pred DocumentNode(dn, l_element, element, grove) :
		DOMObject(dn, $l_dnp) *
		((dn, "@element") -> l_element) * DocumentElement(l_element, element) *
		((dn, "@grove") -> #l_grove) * Grove(#l_grove, grove) *
		empty_fields(dn : "@proto", "@class", "@extensible", "@element", "@grove");

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
		empty_fields($l_enp : "@proto", "@class", "@extensible", "tagName", "getAttribute", "setAttribute", "removeAttribute", "getAttributeNode",
			"setAttributeNode", "removeAttributeNode", "getElementsByTagName");

	@pred ElementNode(name, en, l_attr, attr, l_children, children) :
		DOMObject(en, $l_enp) *
		((en, "@name") -> name) *
		((en, "@attributes") -> l_attr) * AttributeSet(l_attr, attr) *
		((en, "@children") -> l_children) * Forest(l_children, children) * 
		types(name: $$string_type, attr: $$list_type, children: $$list_type) *
		empty_fields(en : "@proto", "@class", "@extensible", "@name", "@attributes", "@children");
	
	@pred ElementNodeSpecial(en, name, attr, children, parent) :
		DOMObject(en, $l_enp) *
		((en, "@name") -> name) *
		((en, "@attributes") -> attr) *
		((en, "@children") -> children) *
		((en, "@parent") -> parent) *
		types(name: $$string_type, attr: $$list_type, children: $$list_type) *
		empty_fields(en : "@proto", "@class", "@extensible", "@name", "@attributes", "@children", "@parent");

	@pred TextNodePrototype() :
		DOMObject($l_tnp, $l_np) *
		(($l_tnp, "@name") -> "#text") *
		DOMFunctionField($l_tnp, "data") *
		DOMFunctionField($l_tnp, "length") *
		DOMFunctionField($l_tnp, "substringData") *
		DOMFunctionField($l_tnp, "appendData") *
		DOMFunctionField($l_tnp, "insertData") *
		DOMFunctionField($l_tnp, "deleteData") *
		DOMFunctionField($l_tnp, "replaceData") *
		DOMFunctionField($l_tnp, "splitText") *
		empty_fields($l_tnp : "@proto", "@class", "@extensible", "@name", "data", "length", "substringData", "appendData",
									 "insertData", "deleteData", "replaceData", "splitText");

	@pred TextNode(tn, text) :
		DOMObject(tn, $l_tnp) *
		((tn, "@text") -> text) *
		empty_fields(tn : "@proto", "@class", "@extensible", "@text");

	@pred AttributeNodePrototype() :
		DOMObject($l_anp, $l_np) *
		empty_fields($l_anp : "@proto", "@class", "@extensible");

	@pred AttributeNode(an, name, l_children, children) :
		DOMObject(an, $l_anp) *
		((an, "@name") -> name) *
		((an, "@children") -> l_children) * TextForest(l_children, children) *
		types(name: $$string_type, children: $$list_type) *
		empty_fields(an : "@proto", "@class", "@extensible", "@name", "@children");

	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();
		
	@pred DocumentElement(l, element) :
		isEmpty(element) * DOMObject(l, $$null) * ((l, "@data") -> $$null) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data"),
		
		isElement(element, #id, #name, #aList, #cList) * DOMObject(l, $$null) * ((l, "@data") -> #id) * 
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * empty_fields(l : "@proto", "@class", "@extensible", "@data"),
	    
	    isHole(element, #alpha) * DOMObject(l, $$null) * ((l, "@data") -> #alpha) * 
	    empty_fields(l : "@proto", "@class", "@extensible", "@data");		

	@pred AttributeSet(l, attrs) : 
	    isEmpty(attrs) * DOMObject(l, $$null) * ((l, "@data") -> $$null) * ((l, "@next") ->  $$null),
	    
	    (attrs == (#head :: #attrsNext)) * isAttr(#head, #name, #id, #tf) * DOMObject(l, $$null) * 
	    ((l, "@data") -> #id) * ((l, "@next") -> #next) * AttributeNode(#name, #id, #l_tf, #tf) * 
	    AttributeSet(#next, #attrsNext) * empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"); 	

	@pred Forest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@data") -> $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * TextNode(#id, #text) * Forest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #aList, #cList) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * Forest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),
		
	    (childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@data") -> #alpha) * ((l, "@next") -> #next) * Forest(#next, #childListNext) *
	    empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next");

	
	@pred TextForest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@data") -> $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * TextNode(#id, #text) * TextForest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
		((l, "@data") -> #alpha) * ((l, "@next") -> #next) * TextForest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next");
	
	@pred Grove(l, content) :
		isEmpty(content) * DOMObject(l, $$null) * ((l, "@data") -> $$null) * ((l, "@next") ->  $$null),
		
		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * TextNode(#id, #text) * Grove(#next, contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #aList, #cList) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * Grove(#next, #contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),	
		
		(content == (#head :: #contentNext)) * isAttr(head, #name, #id, #tList) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * AttributeNode(#id, #name, #l_tf, #tList) * Grove(#next, #contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),	
			
	    (content == (#head :: #contentNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@data") -> #alpha) * ((l, "@next") -> #next) * Grove(#next, #contentNext) *
	    empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next");

	@onlyspec allocAS(l, i, j)
		pre:  [[ (l == #l) * (i == #i) * (j == #j) * 
		         AttributeSet(#l, #as) * (#as == #as1 @ (#as2 @ #as3)) * (l-len(#as1) == #i) * (l-len(#as2) == #j)]]
		post: [[ AttributeSet(#l, (#as1 @ ({{"hole", #alpha}} @ #as3))) * 
		         AttributeSet(#alpha, #as2) * (ret == #alpha) * types(#alpha : $$object_type) ]]
		outcome: normal

	@onlyspec deallocAS(alpha)
		pre:  [[ (alpha == #alpha) * AttributeSet(#l, #as) * (#as == #as1 @ ({{"hole", #alpha}} @ #as3)) * AttributeSet(#alpha, #as2) * types(#alpha : $$object_type)]]
		post: [[ AttributeSet(#l, (#as1 @ (#as2 @ #as3))) ]]
		outcome: normal

	@onlyspec createElement(x)
		pre:  [[ (x == #name) *  DocumentNode(this, #l_element, #element, #g) ]]
		post: [[ (ret == #ret) * DocumentNode(this, #l_element, #element, ({{ {{ "elem", #name, #ret, {{}}, {{}} }} }} @ #g)) * types(#ret : $$object_type) ]]
		outcome: normal

	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * (ret == #t) ]]
		outcome: normal
*/

/**
	@id singleGet
	@rec false

	@pre (
		scope(allocAS   : #allocAS)   * fun_obj(allocAS,   #allocAS,   #allocAS_proto) *
		scope(deallocAS : #deallocAS) * fun_obj(deallocAS, #deallocAS, #deallocAS_proto) *
		(element == #en) * (l_attr == #l_attr) * types (#en : $$object_type, #l_attr : $$object_type) *
		InitialDOMHeap() *
		ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) *
		(#attr == {{ 
			{{ "attr", "src", #a0, #atf0 }}, 
			{{ "attr", "width", #a1, #atf1 }}, 
			{{ "attr", "height", #a2, #atf2 }}, 
			{{ "hole", #a_alpha2 }} 
		}})
	)
	
	@post (
		fun_obj(allocAS,   #allocAS,   #allocAS_proto) *
		fun_obj(deallocAS, #deallocAS, #deallocAS_proto) *
		ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) *
		InitialDOMHeap() *
		(#attr == {{ 
			{{ "attr", "src", #a0, #atf0 }}, 
			{{ "attr", "width", #a1, #atf1 }}, 
			{{ "attr", "height", #a2, #atf2 }},
			{{ "hole", #a_alpha2 }} 
		}})
	)
*/
function singleGet(element, l_attr) {
	/* @unfold ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) */
	var a = allocAS(l_attr, 1, 3);
	var w = element.getAttribute("src");
	deallocAS(a);
}

/** 
	@toprequires (DocumentNode($l_document, #l_element, {{ }}, {{ }}) * InitialDOMHeap() * scope(document : $l_document))
	@topensures  (DocumentNode($l_document, #l_element, {{ }}, {{ {{ "elem", "one", #ret, {{}}, {{}} }} }}) * InitialDOMHeap() * scope(document : $l_document))
*/
document.createElement("one");
