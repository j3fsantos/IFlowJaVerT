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

	@pred DocumentNode(dn, element) :
		DOMObject(dn, $l_dnp) *
		((dn, "@element") -> element) *
		empty_fields(dn : "@proto", "@class", "@extensible", "@element");

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

	@pred ElementNode(en, name, attr, children) :
		DOMObject(en, $l_enp) *
		((en, "@name") -> name) *
		((en, "@attributes") -> attr) *
		((en, "@children") -> children) *
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

	@pred AttributeNode(an, name, children) :
		DOMObject(an, $l_anp) *
		((an, "@name") -> name) *
		((an, "@children") -> children) *
		types(name: $$string_type, children: $$list_type) *
		empty_fields(an : "@proto", "@class", "@extensible", "@name", "@children");

	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();
		
	@pred DocumentElement(l, element) :
		isEmpty(element) * DOMObject(l, $$null) * ((l, "@data") -> $$null) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data"),
		
		isElement(element, #id, #name, #aList, #cList) * DOMObject(l, $$null) * ((l, "@data") -> #id) * 
		ElementNode(#id, #name, #aList, #cList) * empty_fields(l : "@proto", "@class", "@extensible", "@data"),
	    
	    isHole(element, #alpha) * DOMObject(l, $$null) * ((l, "@data") -> #alpha) * 
	    empty_fields(l : "@proto", "@class", "@extensible", "@data");		

	@pred AttributeSet(l, attrs) : 
	    isEmpty(attrs) * DOMObject(l, $$null) * ((l, "@data") -> $$null) * ((l, "@next") ->  $$null),
	    
	    (attrs == (#head :: #attrsNext)) * isAttr(#head, #name, #id, #tf) * DOMObject(l, $$null) * 
	    ((l, "@data") -> #id) * ((l, "@next") -> #next) * AttributeNode(#name, #id, #tf) * 
	    AttributeSet(#next, #attrsNext) * empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"); 	

	@pred Forest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@data") -> $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * TextNode(#id, #text) * Forest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #aList, #cList) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * ElementNode(#id, #name, #aList, #cList) * Forest(#next, #childListNext) *
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
		((l, "@data") -> #id) * ((l, "@next") -> #next) * ElementNode(#id, #name, #aLit, #cList) * Grove(#next, #contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),	
		
		(content == (#head :: #contentNext)) * isAttr(head, #name, #id, #tList) * DOMObject(l, $$null) *
		((l, "@data") -> #id) * ((l, "@next") -> #next) * AttributeNode(#id, #name, #tList) * Grove(#next, #contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next"),	
			
	    (content == (#head :: #contentNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@data") -> #alpha) * ((l, "@next") -> #next) * Grove(#next, #contentNext) *
	    empty_fields(l : "@proto", "@class", "@extensible", "@data", "@next");
*/

/** 
	@toprequires (InitialDOMHeap() * DocumentNode($l_document, $$null) * scope(document : $l_document))
	@topensures  (InitialDOMHeap() * DocumentNode($l_document, $$null) * scope(document : $l_document))
*/
document.createElement("one");
document.createElement("two");
