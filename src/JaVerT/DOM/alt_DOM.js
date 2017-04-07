/**
	@pred isEmpty (l) :
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

	@pred DocumentNode(dn) :
		DOMObject(dn, $l_dnp) *
		empty_fields(dn : );

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

	@pred ElementNode(en) :
		DOMObject(en, $l_enp) *
		empty_fields(en : );

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

	@pred TextNode(tn) :
		DOMObject(tn, $l_tnp) *
		empty_fields(tn : );

	@pred AttributeNodePrototype() :
		DOMObject($l_anp, $l_np) *
		empty_fields($l_anp :);

	@pred AttributeNode(name, an, l_children, children) :
		DOMObject(an, $l_anp) *
		((an, "@name") -> name) *
		((an, "@children") -> l_children) *
		types(name: $$string_type, children: $$list_type) *
		empty_fields(an : "@name", "@children");

	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();
		
	@pred DocumentElement(l, element) :
		(element == {{ }}) * DOMObject(l, $$null) * empty_fields(l :),
		
		(element == {{ {{ "elem", #id, #name, #l_a, #l_c }} }}) * isElement(element, #id, #name, #l_a, #l_c) * 
		DOMObject(l, $$null) * empty_fields(l :),
	    
	    isHole(element, #alpha) * DOMObject(l, $$null) * empty_fields(l :);		

	@pred AttributeSet(l, attrs) : 
	    isEmpty(attrs) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
	    
	    (attrs == (#head :: #attrsNext)) * isAttr(#head, #name, #id, #l_tf) * DOMObject(l, $$null) * 
	    ((l, "@next") -> #next) * AttributeSet(#next, #attrsNext) * empty_fields(l : "@next"); 	

	@pred Forest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * Forest(#next, #childListNext) * empty_fields(l : "@next"),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #l_a, #l_c) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * Forest(#next, #childListNext) * empty_fields(l : "@next"),
		
	    (childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@next") -> #next) * Forest(#next, #childListNext) * empty_fields(l : "@next");

	
	@pred TextForest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextForest(#next, #childListNext) * empty_fields(l : "@next"),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextForest(#next, #childListNext) * empty_fields(l : "@next");
	
	@pred Grove(l, content) :
		isEmpty(content) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * Grove(#next, contentNext) * empty_fields(l : "@next"),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #l_a, #l_c) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * Grove(#next, #contentNext) * empty_fields(l : "@next"),
		
		(content == (#head :: #contentNext)) * isAttr(head, #name, #id, #l_tf) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * Grove(#next, #contentNext) * empty_fields(l : "@next"),
			
	    (content == (#head :: #contentNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@next") -> #next) * Grove(#next, #contentNext) * empty_fields(l : "@next");


	@pred val(t, s) :
		isEmpty(t) * (s == ""),
		(t == (#head :: #childListNext)) * isText(#head, #id, #s1) * val(#childListNext, #s2) * (s == #s1 ++ #s2);

	@pred out(a, s) :
		isEmpty(a),
		(a == (#head :: #childListNext)) * isAttr(#head, #name, #id, #l_tf) * (! (s == #name)) * 
		out(#childListNext, s) * types(s: $$string_type, #name: $$string_type);

	@pred complete(l) :
		isEmpty(l),
		(l == (#head :: #next)) * isText(#head, #id, #s1) * complete(#next),
		(l == (#head :: #next)) * isAttr(#head, #n, #id, #l_tf) * complete(#next),
		(l == (#head :: #next)) * isElement(#head, #n, #id, #l_a, #l_c) * complete(#next);

	@pred grove_or_forest(l, e) :
		Grove(l, e),
		Forest(l, e);

	@pred Cell(l, e) :
		Grove(l, e),
		Forest(l, e),
		TextForest(l, e),
		DocumentElement(l, e),
		AttributeSet(l, e);


	@onlyspec allocAS(l, i, j)
		pre:  [[ (l == #l) * (i == #i) * (j == #j) * types (#as : $$list_type, #as1 : $$list_type, #as2 : $$list_type, #as3 : $$list_type) *
		         AttributeSet(#l, #as) * (#as == #as1 @ (#as2 @ #as3)) * (l-len(#as1) == #i) * (l-len(#as2) == #j) ]]
		post: [[ AttributeSet(#l, (#as1 @ ({{ "hole", #alpha }} :: #as3))) * 
		         AttributeSet(#alpha, #as2) * (ret == #alpha) * types(#alpha : $$object_type) ]]
		outcome: normal

	@onlyspec deallocAS(alpha)
		pre:  [[ (alpha == #alpha) * AttributeSet(#l, #as) * (#as == #as1 @ ({{ "hole", #alpha }} :: #as3)) * AttributeSet(#alpha, #as2) * types(#alpha : $$object_type)]]
		post: [[ AttributeSet(#l, (#as1 @ (#as2 @ #as3))) * (ret == $$empty) ]]
		outcome: normal

	@onlyspec allocG(l, i, j)
		pre:  [[ (l == #l) * (i == #i) * (j == #j) * types(#g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ (#g2 @ #g3)) * (l-len(#g1) == #i) * (l-len(#g2) == #j) ]]
		post: [[ Grove(#l, (#g1 @ ({{ "hole", #alpha }} :: #g3))) * Grove(#alpha, #g2) * (ret == #alpha) * types(#alpha : $$object_type)]]
		outcome: normal;

		pre:  [[ (l == #l) * (i == 0) * (j == #j) * types(#g : $$list_type) * Grove(#l, #g) ]]
		post: [[ Grove(#l, ({{"hole", #alpha}} :: #g)) * Grove(#alpha, {{ }}) * (ret == #alpha) ]]
		outcome: normal

	@onlyspec deallocG(alpha)
		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{"hole", #alpha}} :: #g3)) * Grove(#alpha, #g2)]]
		post: [[ Grove(#l, (#g1 @ (#g2 @ #g3))) * (ret == $$empty) ]]
		outcome: normal

*/ /*
	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * AttributeSet(#l_attr, #attr) *
				 (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * val(#t, #s1) * types(#s1 : $$string_type) ]]
		post: [[ (s == #s) * Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * AttributeSet(#l_attr, #attr) *
				 (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * (ret == #s1) ]]
		outcome: normal;
		
		pre:  [[ (s == #s) * Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * 
				 AttributeSet(#l_attr, #attr) * out(#attr, #s) ]]
		post: [[ (s == #s) * Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * 
				 AttributeSet(#l_attr, #attr) * (ret == "")    ]]
		outcome: normal

	@onlyspec setAttribute(s, v)
		pre:  [[ Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * 
				 AttributeSet(#l_attr, #attr) * (s == #s1) * (v == #s2) * 
				 (#attr == {{ {{ "attr", #s1, #m, #l_tf }}, {{ "hole", #alpha }} }}) * AttributeNode(#s1, #m, #l_tf) *
				 TextForest(#l_tf, #t) * Grove(#l_g, {{ }}) ]]
		post: [[ Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * AttributeSet(#l_attr, #attr_post) *
				 (#attr_post == {{ {{ "attr", #s1, #m, #l_tf_post }}, {{ "hole", #alpha }} }}) * AttributeNode(#s1, #m, #l_tf_post) * 
				 TextForest(#l_tf_post, #t_post) * (#t_post == {{ {{ "text", #r, #s2 }} }}) * 
				 TextNode(#r, #s2) * Grove(#l_g, #t) ]]
		outcome: normal;

		pre:  [[ Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * 
				 AttributeSet(#l_attr, #attr) * (s == #s1) * (v == #s2) * out(#attr, #s1) ]]
		post: [[ Cell(#l, {{ {{ "elem", #name, this, #l_attr, #l_children }} }}) * ElementNode(this) * 
				 AttributeSet(#l_attr, #attr2) * (#attr2 == {{ "attr", #s1, #m, #l_tf }} :: #attr) * 
				 AttributeNode(#s1, #m, #l_tf) * (#t == {{ {{ "text", #r, #s2 }} }}) ]]
		outcome: normal
*/