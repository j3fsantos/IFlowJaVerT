/*
	NOTE: File contains only the two DOM function specifications necessary.
	The rest are removed to improve run speed. Complete functions in prealloc_DOM.js
*/ /*

	@pred isNil(l) :
		l == {{ }};
	
	@pred isHole(l, alpha) :
		l == {{ "hole", alpha }};
	
	@pred isText(l, id, txt) :
		l == {{ "text", id, txt }};
	
	@pred isElement(l, name, id, aList, cList) :
		l == {{ "elem", name, id, aList, cList }};
	
	@pred isAttr(l, name, id, tfList) :
		(l == {{ "attr", name, id, tfList }});

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

	@pred AttributeNodePrototype() :
		DOMObject($l_anp, $l_np) *
		empty_fields($l_anp :);


	@pred DocumentNode(dn, l_element, element, l_grove, grove) :
		DOMObject(dn, $l_dnp) *
		((dn, "@element") -> l_element) * DocumentElement(l_element, element) *
		((dn, "@grove") -> l_grove) * Grove(l_grove, grove) *
		empty_fields(dn : "@element", "@grove");

	@pred ENode(alpha, name, id, l_attr, aList, l_children, cList) :
		DOMObject(id, $l_enp) * ((id, "@address") -> alpha) * empty_fields(id : "@name", "@attributes", "@children", "@address") * 
		ElementNode(name, id, l_attr, aList, l_children, cList);

	@pred ElementNode(name, id, l_attr, aList, l_children, cList) :
		((id, "@name") -> name) *
		((id, "@attributes") -> l_attr) * AttributeSet(l_attr, aList) *
		((id, "@children") -> l_children) * Forest(l_children, cList) * 
		types(name: $$string_type, aList: $$list_type, cList: $$list_type); 

	@pred TNode(alpha, id, text) :
		DOMObject(id, $l_tnp) * ((id, "@address") -> alpha) * empty_fields(id : "@text", "@address") *
		TextNode(id, text);

	@pred TextNode(id, text) :
		((id, "@text") -> text) *
		types(text: $$string_type);

	@pred ANode(name, id, l_children, cList) :
		DOMObject(id, $l_anp) * empty_fields(id : "@name", "@children") *
		AttributeNode(name, id, l_children, cList);

	@pred AttributeNode(name, id, l_children, cList) :
		((id, "@name") -> name) *
		((id, "@children") -> l_children) * TextForest(l_children, cList);

	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();

*/ /*
	----DOM Derived assertions----
*/ /*

	@pred val(t, s) :
		isNil(t) * (s == ""),
		(t == (#head :: #childListNext)) * isText(#head, #id, #s1) * val(#childListNext, #s2) * (s == #s1 ++ #s2),
		(t == (#head :: #childListNext)) * isHole(#head, #alpha) * TCell(#alpha, #id, #s1) * val(#childListNext, #s2) * (s == #s1 ++ #s2);

	@pred out(a, s) :
		isNil(a),
		(a == (#head :: #childListNext)) * isAttr(#head, #name, #id, #l_tf) * (! (s == #name)) * 
		out(#childListNext, s) * types(s: $$string_type, #name: $$string_type),
		(a == (#head :: #childListNext)) * isHole(#head, #alpha) * ACell(#alpha, #name, #id, #l_tf, #tf) * (! (s == #name)) * 
		out(#childListNext, s) * types(s: $$string_type, #name: $$string_type);

	@pred complete(l) :
		isNil(l),
		(l == (#head :: #next)) * isText(#head, #id, #s1) * complete(#next),
		(l == (#head :: #next)) * isElement(#head, #n, #id, #l_a, #l_c) * complete(#next) * complete(#l_c),
		(l == (#head :: #next)) * isHole(#head, #alpha) * TCell(#alpha, #id, #s1) * complete(#next),
		(l == (#head :: #next)) * isHole(#head, #alpha) * ECell(#alpha, #n, #id, #l_a, #a, #l_c, #c) * complete(#next) * complete(#c);

*/ /*
	----DOM Structural Data----
*/ /*

	@pred ChainCell(l, next, content) : 
		((l, "@next") -> next) * ((l, "@content") -> content);

	@pred DocumentElement(l, element) :
		isNil(element) * DOMObject(l, $$null) * empty_fields(l :),
		
		(element == (#head :: {{}})) * isElement(#head, #id, #name, #l_a, #l_c) * 
		DOMObject(l, $$null) * empty_fields(l :),
		
		(element == (#head :: {{}})) * isHole(#head, #alpha) * DOMObject(l, $$null) * empty_fields(l :);


	@pred AttributeSet(alpha, attrs) : 
		((alpha, "@chain") ->  #l) * empty_fields(alpha : "@chain") * AttributeSetRec(#l, attrs);

	@pred AttributeSetRec(l, attrs) : 
		isNil(attrs) * (l == $$null),
		
		(attrs == (#head :: #attrsNext)) * isAttr(#head, #name, #id, #tfList) * 
		DOMObject(#id, $l_anp) * empty_fields(#id : "@name", "@children") *
		AttributeNode(#name, #id, #l_tf, #tfList) * 
		ChainCell(l, #next, #id) * AttributeSetRec(#next, #attrsNext), 

		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * AttributeSetRec(#next, #childListNext); 	


	@pred Forest(alpha, childList) : 
		((alpha, "@chain") ->  #l) * ForestRec(#l, childList);

	@pred ForestRec(l, childList) :
		isNil(childList) * (l == $$null),

		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * 
		DOMObject(#id, $l_tnp) * empty_fields(#id : "@text") * TextNode(#id, #text) *
		ChainCell(l, #next, #id) * ForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #aList, #cList) * 
		DOMObject(#id, $l_enp) * empty_fields(#id : "@name", "@attributes", "@children") *
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) *
		ChainCell(l, #next, #id) * ForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * ForestRec(#next, #childListNext);


	@pred TextForest(alpha, content) : 
		((alpha, "@chain") ->  #l) * TextForestRec(alpha, #l, content);
	
	@pred TextForestRec(root, l, content) :
		isNil(content) * (l == $$null),

		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * 
		DOMObject(#id, $l_tnp) * empty_fields(#id : "@text") * TextNode(#id, #text) *
		((l, "@address") -> root) * ChainCell(l, #next, #id) * TextForestRec(root, #next, #contentNext),
		
		(content == (#head :: #contentNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * TextForestRec(root, #next, #contentNext);


	@pred Grove(alpha, content) : 
		((alpha, "@chain") ->  #l) * GroveRec(alpha, #l, content) * types(content : $$list_type, #l: $$object_type);	
	
	@pred GroveRec(root, l, content) :
		isNil(content)  * (l == $$null),

		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * 
		DOMObject(#id, $l_tnp) * empty_fields(#id : "@text") * TextNode(#id, #text) * 
		((l, "@address") -> root) * ChainCell(l, #next, #id) * GroveRec(#next, #contentNext),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #aList, #cList) * 
		DOMObject(#id, $l_enp) * empty_fields(#id : "@name", "@attributes", "@children") *
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) *
		((l, "@address") -> root) * ChainCell(l, #next, #id) * GroveRec(#next, #contentNext),

		(content == (#head :: #contentNext)) * isAttr(#head, #name, #id, #tfList) * 
		DOMObject(#id, $l_anp) * empty_fields(#id : "@name", "@children") *
		AttributeNode(#name, #id, #l_tf, #tfList) * 
		((l, "@address") -> root) * ChainCell(l, #next, #id) * GroveRec(#next, #contentNext),
		
		(content == (#head :: #contentNext)) * isHole(#head, #alpha) *
		((l, "@address") -> root) * ChainCell(l, #next, #alpha) * GroveRec(#next, #contentNext);



	@pred ECell(alpha, name, id, l_attr, aList, l_children, cList) : 
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, id) * types(#l: $$object_type) *
		DOMObject(id, $l_enp) * ((id, "@address") -> alpha) * empty_fields(id : "@name", "@attributes", "@children", "@address") * 
		ElementNode(name, id, l_attr, aList, l_children, cList);

	@pred TCell(alpha, id, text) : 
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, id) *
		((id, "@address") -> alpha) * DOMObject(id, $l_tnp) * empty_fields(id : "@text", "@address") * 
		TextNode(id, text);

	@pred ACell(alpha, name, id, l_children, cList) : 
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, id) * 
		DOMObject(id, $l_anp) * ((id, "@address") -> alpha) * empty_fields(id : "@name", "@children", "@address") *
		AttributeNode(name, id, l_children, cList);	

	@pred EmptyCell(alpha) :
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, $$null);

*/ /*
	----Element Node Axioms----
*/ /*

	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * ECell(#alpha, #name, this, #l_aList, #aList, #l_children, #cList) *
				 (#aList == #a1 @ ({{ "hole", #gamma }} :: #a2)) * ACell(#gamma, #s, #m, #l_t, #t) * val(#t, #s1) * types(#s1 : $$string_type) ]]
		post: [[ ECell(#alpha, #name, this, #l_aList, #aList, #l_children, #cList) * ACell(#gamma, #s, #m, #l_t, #t) * val(#t, #s1) * (ret == #s1) ]]
		outcome: normal;

		pre:  [[ (s == #s) * ECell(#alpha, #name, this, #l_aList, #aList, #l_children, #cList) * out(#aList, #s) ]]
		post: [[ ECell(#alpha, #name, this, #l_aList, #aList, #l_children, #cList) * (ret == "")     ]]
		outcome: normal


	@onlyspec setAttribute(s, v)
		pre:  [[ (s == #s1) * (v == #s2) * ECell(#alpha, #name, this, #l_aList, #aList, #l_children, #cList) * 
				 (#aList == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 ACell(#gamma, #s1, #m, #l_t, #t) * Grove(#beta, #g) ]]
		post: [[ ECell(#alpha, #name, this, #l_aList, #aList_post, #l_children, #cList) * 
				 (#aList_post == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 ACell(#gamma, #s1, #m, #l_t, {{ {{ "hole", #gamma2 }} }}) * 
				 TCell(#gamma2, #r, #s2) * Grove(#beta, #g_post) * (#g_post == #t @ #g) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ECell(#alpha, #name, this, #l_aList, #aList, #l_children, #cList) * 
				 (s == #s1) * (v == #s2) * out(#aList, #s1) ]]
		post: [[ ECell(#alpha, #name, this, #l_aList, #aList_post, #l_children, #cList) * 
				 (#aList_post == {{ "hole", #gamma }} :: #aList) * 
				 ACell(#gamma, #s1, #m, #l_t, {{ {{ "hole", #gamma2 }} }}) * 
				 TCell(#gamma2, #r, #s2) * (ret == $$null) ]]
		outcome: normal

*/

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