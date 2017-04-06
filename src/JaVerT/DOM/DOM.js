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
		(l == {{ "attr", name, id, tf }});

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
		(($l_dnp, "@name") -> "#document") *
		DOMFunctionField($l_dnp, "documentElement") *
		DOMFunctionField($l_dnp, "createElement") *
		DOMFunctionField($l_dnp, "createTextNode") *
		DOMFunctionField($l_dnp, "createAttribute") *
		DOMFunctionField($l_dnp, "getElementsByTagName") *
		empty_fields($l_dnp : "@name", "documentElement", "createElement", "createTextNode", "createAttribute", "getElementsByTagName");

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
		types(name: $$string_type, attr: $$list_type, children: $$list_type) *
		empty_fields(en : "@name", "@attributes", "@children");

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
		empty_fields($l_tnp : "@name", "data", "length", "substringData", "appendData",
									 "insertData", "deleteData", "replaceData", "splitText");

	@pred TextNode(tn, text) :
		DOMObject(tn, $l_tnp) *
		((tn, "@text") -> text) *
		empty_fields(tn : "@text");

	@pred AttributeNodePrototype() :
		DOMObject($l_anp, $l_np) *
		empty_fields($l_anp :);

	@pred AttributeNode(name, an, l_children, children) :
		DOMObject(an, $l_anp) *
		((an, "@name") -> name) *
		((an, "@children") -> l_children) * TextForest(l_children, children) *
		types(name: $$string_type, children: $$list_type) *
		empty_fields(an : "@name", "@children");

	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();
		
	@pred DocumentElement(l, element) :
		isEmpty(element) * DOMObject(l, $$null) *
		empty_fields(l :),
		
		isElement(element, #id, #name, #aList, #cList) * DOMObject(l, $$null) *
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * empty_fields(l :),
	    
	    isHole(element, #alpha) * DOMObject(l, $$null) *
	    empty_fields(l :);		

	@pred AttributeSet(l, attrs) : 
	    isEmpty(attrs) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
	    
	    (attrs == (#head :: #attrsNext)) * isAttr(#head, #name, #id, #tf) * DOMObject(l, $$null) * 
	    ((l, "@next") -> #next) * AttributeNode(#name, #id, #l_tf, #tf) * AttributeSet(#next, #attrsNext) * 
	    empty_fields(l : "@next"); 	

	@pred Forest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextNode(#id, #text) * Forest(#next, #childListNext) *
		empty_fields(l : "@next"),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #aList, #cList) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * Forest(#next, #childListNext) *
		empty_fields(l : "@next"),
		
	    (childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@next") -> #next) * Forest(#next, #childListNext) *
	    empty_fields(l : "@next");

	
	@pred TextForest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextNode(#id, #text) * TextForest(#next, #childListNext) *
		empty_fields(l : "@next"),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextForest(#next, #childListNext) *
		empty_fields(l : "@next");
	
	@pred Grove(l, content) :
		isEmpty(content) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextNode(#id, #text) * Grove(#next, contentNext) *
		empty_fields(l : "@next"),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #aList, #cList) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * Grove(#next, #contentNext) *
		empty_fields(l : "@next"),	
		
		(content == (#head :: #contentNext)) * isAttr(head, #name, #id, #tList) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * AttributeNode(#name, #id, #l_tf, #tList) * Grove(#next, #contentNext) *
		empty_fields(l : "@next"),	
			
	    (content == (#head :: #contentNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@next") -> #next) * Grove(#next, #contentNext) *
	    empty_fields(l : "@next");


	@pred val(t, s) :
		isEmpty(t) * (s == ""),
		(t == (#head :: #childListNext)) * isText(#head, #id, #s1) * val(#childListNext, #s2) * (s == #s1 ++ #s2);

	@pred out(a, s) :
		isEmpty(a),
		(a == (#head :: #childListNext)) * isAttr(#head, #name, #id, #tf) * (! (s == #name)) * out(#childListNext, s) * types(s: $$string_type, #name: $$string_type);

	@pred complete(l) :
		isEmpty(l),
		(l == (#head :: #next)) * isText(#head, #id, #s1) * complete(#next),
		(l == (#head :: #next)) * isAttr(#head, #n, #id, #tf) * complete(#next),
		(l == (#head :: #next)) * isElement(#head, #n, #id, #a, #c) * complete(#next);

	@pred grove_or_forest(e) :
		Grove(#alpha, #l) * (#l == {{ e }}),
		Forest(#alpha, #l) * (#l == {{ e }});


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
	----General Axioms----
*/ /*
	@onlyspec nodeName()
		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == "#document") ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (ret == #name) * types(#name : $$string_type) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == "#text") ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == #name) * types(#name : $$string_type) ]]
		outcome: normal

	@onlyspec nodeValue()
		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #t) ]]
		post: [[ TextNode(this, #t) * (ret == #t) * types(#t: $$string_type) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) * val(#children, #s1) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == #s1) * types(#s1 : $$string_type) ]]
		outcome: normal

	@onlyspec parentNode()
		pre:  [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) ]]
		post: [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) * (ret == #dn) * types(#dn : $$object_type) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha2 }} }}) ]]
		post: [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha2 }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "text", this, #t }}, {{ "hole", #alpha2 }} }}) ]]
		post: [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "text", this, #t }}, {{ "hole", #alpha2 }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, #an, #l_children, #children) * (#children == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ AttributeNode(#name, #an, #l_children, #children) * (#children == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) * (ret == #an) * types(#an : $$object_type) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "hole", #alpha1 }}, {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha2 }} }}) ]]
		post: [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "hole", #alpha1 }}, {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha2 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "hole", #alpha1 }}, {{ "text", this, #t }}, {{ "hole", #alpha2 }} }}) ]]
		post: [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "hole", #alpha1 }}, {{ "text", this, #t }}, {{ "hole", #alpha2 }} }}) * (ret == $$null) ]]
		outcome: normal


	@onlyspec firstChild()
		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, {{ }}, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, {{ }}, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "hole", #alpha }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;
		
		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, {{ }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec lastChild()
		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, {{ }}, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, {{ }}, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;
		
		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, {{ }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec previousSibling()
		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t }}, {{ "elem", #name, this, #en_attr, #en_children }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t }}, {{ "elem", #name, this, #en_attr, #en_children }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "text", this, #t }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "text", this, #t }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, #en, #a1, #c1 }}, {{ "elem", #n2, this, #a2, #c2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, #en, #a1, #c1 }}, {{ "elem", #n2, this, #a2, #c2 }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t1 }}, {{ "text", this, #t2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t1 }}, {{ "text", this, #t2 }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "text", this, #t1 }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "text", this, #t1 }}, {{ "hole", #alpha }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "hole", #alpha }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) ]]
		post: [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #g) * (#g == {{ {{ "elem", #n1, this, #a1, #c1 }} }}) ]]
		post: [[ Grove(#alpha, #g) * (#g == {{ {{ "elem", #n1, this, #a1, #c1 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #g) * (#g == {{ {{ "text", this, #t }} }}) ]]
		post: [[ Grove(#alpha, #g) * (#g == {{ {{ "text", this, #t }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ TextForest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t1 }}, {{ "text", this, #t2 }} }}) ]]
		post: [[ TextForest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t1 }}, {{ "text", this, #t2 }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec nextSibling()
		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, this, #en_attr, #en_children }}, {{ "text", #tn, #t }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, this, #en_attr, #en_children }}, {{ "text", #tn, #t }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "elem", #n2, #en, #a2, #c2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "elem", #n2, #en, #a2, #c2 }} }}) * (ret == #en) * types(#en : $$object_type) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t1 }}, {{ "text", #tn, #t2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t1 }}, {{ "text", #tn, #t2 }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", this, #t1 }} }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", this, #t1 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #n1, this, #a1, #c1 }}  }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #n1, this, #a1, #c1 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) ]]
		post: [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #g) * (#g == {{ {{ "elem", #n1, this, #a1, #c1 }} }}) ]]
		post: [[ Grove(#alpha, #g) * (#g == {{ {{ "elem", #n1, this, #a1, #c1 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #g) * (#g == {{ {{ "text", this, #t }} }}) ]]
		post: [[ Grove(#alpha, #g) * (#g == {{ {{ "text", this, #t }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ TextForest(#alpha, #f) * (#f == {{ {{ "text", this, #t1 }}, {{ "text", #tn, #t2 }} }}) ]]
		post: [[ TextForest(#alpha, #f) * (#f == {{ {{ "text", this, #t1 }}, {{ "text", #tn, #t2 }} }}) * (ret == #tn) * types(#tn : $$object_type) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "hole", #alpha }}, {{ "text", this, #t }} }}) ]]
		post: [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "hole", #alpha }}, {{ "text", this, #t }} }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec ownerDocument()
		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l, #a, #l_children, #children) ]]
		post: [[ ElementNode(#name, this, #l, #a, #l_children, #children) * (ret == $l_document) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == $l_document) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == $l_document) ]]
		outcome: normal

	@onlyspec insertBefore(m, n)
		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "elem", #ename2, #n, #a2, #c2 }} }}) * complete(#c2) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename2, #n, #a2, #c2 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "elem", #ename2, #n, #a2, #c2 }} }}) * complete(#c2) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename2, #n, #a2, #c2 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #n, #t2 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t2 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "text", #n, #t2 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t2 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "elem", #ename2, #n, #a2, #c2 }} }}) * complete(#c2) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename2, #n, #a2, #c2 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "elem", #ename2, #n, #a2, #c2 }} }}) * complete(#c2) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename2, #n, #a2, #c2 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #n, #t2 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t2 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "text", #n, #t2 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t2 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (m == $$null) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) * complete(#c1) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }}, {{ "elem", #ename1, #n, #a1, #c1 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == $$null) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) * complete(#c1) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }}, {{ "elem", #ename1, #n, #a1, #c1 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (m == $$null) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == $$null) * (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (m == #m) * (n == #n) * AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #n, #t2 }} }}) ]]
		post: [[ AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t2 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == #m) * (n == #n) * AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "text", #n, #t2 }} }}) ]]
		post: [[ AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t2 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		
		pre:  [[ (m == $$null) * (n == #n) * AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == $$null) * (n == #n) * AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (m == $$null) * (n == #n) * DocumentNode(this, #l_e, #e, #l_g, #g) * 
				 (#e == {{ }}) *
				 Grove(#alpha, #g2) * (#g2 == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) ]]
		post: [[ DocumentNode(this, #l_e, #e, #l_g, #g) * 
				 (#e == {{ "elem", #ename1, #n, #a1, #c1 }}) *
				 Grove(#alpha, #g2) * (#g2 == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (m == $$null) * (n == #n) * DocumentNode(this, #l_e, #e, #l_g, #g) * 
				 (#e == {{ }}) *
				 Forest(#alpha, #g2) * (#g2 == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) ]]
		post: [[ DocumentNode(this, #l_e, #e, #l_g, #g) * 
				 (#e == {{ "elem", #ename1, #n, #a1, #c1 }}) *
				 Forest(#alpha, #g2) * (#g2 == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal

	@onlyspec replaceChild(n, o)
		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s2, #o, #a2, #c2 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ {{ "elem", #s1, #n, #a1, #c1 }} }}) * complete(#c1) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s1, #n, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "elem", #s2, #o, #a2, #c2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s2, #o, #a2, #c2 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ {{ "elem", #s1, #n, #a1, #c1 }} }}) * complete(#c1) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s1, #n, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "elem", #s2, #o, #a2, #c2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s2, #o, #a2, #c2 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "elem", #s2, #o, #a2, #c2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s2, #o, #a2, #c2 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "elem", #s2, #o, #a2, #c2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t2 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ {{ "elem", #s1, #n, #a1, #c1 }} }}) * complete(#c1) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s1, #n, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "text", #o, #t2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t2 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ {{ "elem", #s1, #n, #a1, #c1 }} }}) * complete(#c1) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s1, #n, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "text", #o, #t2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t2 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l == {{ {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "text", #o, #t2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t2 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "text", #o, #t2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (n == #n) * (o == #o) * AttributeNode(#s, this, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t2 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ AttributeNode(#s, this, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "text", #o, #t2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * (o == #o) * AttributeNode(#s, this, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t2 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ AttributeNode(#s, this, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #n, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "text", #o, #t2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (n == #n) * (o == #o) * DocumentNode(this, #l_c, #c, #l_g, #g) *
				 (#c == {{ "elem", #s2, #o, #a2, #c2 }}) *
				 Grove(#alpha1, #l1) * (#l == {{ {{ "elem", #s1, #n, #a1, #c1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ DocumentNode(this, #l_c, #c, #l_g, #g) *
				 (#c == {{ "elem", #s1, #n, #a1, #c1 }}) *
				 Grove(#alpha1, #l1) * (#l1 == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "elem", #s2, #o, #a2, #c2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * (o == #o) * DocumentNode(this, #l_c, #c, #l_g, #g) *
				 (#c == {{ "elem", #s2, #o, #a2, #c2 }}) *
				 Forest(#alpha1, #l1) * (#l1 == {{ {{ "elem", #s1, #n, #a1, #c1 }} }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ }}) ]]
		post: [[ DocumentNode(this, #l_c, #c, #l_g, #g) *
				 (#c == {{ "elem", #s1, #n, #a1, #c1 }}) *
				 Forest(#alpha1, #l1) * (#l == {{ }}) *
				 Grove(#alpha2, #l2) * (#l2 == {{ {{ "elem", #s2, #o, #a2, #c2 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal

	@onlyspec removeChild(o)
		pre:  [[ (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "elem", #s1, #o, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "elem", #s1, #o, #a1, #c1 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (o == #o) * ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) ]]
		post: [[ ElementNode(#s, this, #l_a, #a, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #o, #t1 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (o == #o) * AttributeNode(#s, this, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "text", #o, #t1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) ]]
		post: [[ AttributeNode(#s, this, #l_c, #c) *
				 (#c == {{ {{ "hole", #gamma1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #o, #t1 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal;

		pre:  [[ (o == #o) * DocumentNode(this, #l_c, #c, #l_g, #g) *
				 (#c == {{ "elem", #s1, #o, #a1, #c1 }}) *
				 Grove(#alpha, #g) * (#g == {{ }}) ]]
		post: [[ DocumentNode(this, #l_c, #c, #l_g, #g) *
				 (#c == {{ }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "elem", #s1, #o, #a1, #c1 }} }}) * (ret == #o) * types(#o : $$object_type) ]]
		outcome: normal

	@onlyspec appendChild(n)
		pre:  [[ (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) * complete(#c1) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec_post) * 
				 (#ec_post == {{ {{ "hole", #gamma }}, {{ "elem", #ename1, #n, #a1, #c1 }} }}) *
				 Grove(#alpha, #g_post) * (#g_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) * complete(#c1) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec_post) * 
				 (#ec_post == {{ {{ "hole", #gamma }}, {{ "elem", #ename1, #n, #a1, #c1 }} }}) *
				 Forest(#alpha, #f_post) * (#f_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec_post) * 
				 (#ec_post == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha, #g_post) * (#g_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec) * 
				 (#ec == {{ {{ "hole", #gamma }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ ElementNode(#ename, this, #l_ea, #ea, #l_ec, #ec_post) * 
				 (#ec_post == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Forest(#alpha, #f_post) * (#f_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		
		pre:  [[ (n == #n) * AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ AttributeNode(#aname, this, #l_ac, #ac_post) * 
				 (#ac_post == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Grove(#alpha, #g_post) * (#g_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * AttributeNode(#aname, this, #l_ac, #ac) * 
				 (#ac == {{ {{ "hole", #gamma }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "text", #n, #t1 }} }}) ]]
		post: [[ AttributeNode(#aname, this, #l_ac, #ac_post) * 
				 (#ac_post == {{ {{ "hole", #gamma }}, {{ "text", #n, #t1 }} }}) *
				 Forest(#alpha, #f_post) * (#f_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;

		pre:  [[ (n == #n) * DocumentNode(this, #l_e, #e, #l_g, #g) * 
				 (#e == {{ }}) *
				 Grove(#alpha, #g2) * (#g2 == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) ]]
		post: [[ DocumentNode(this, #l_e, #e_post, #l_g, #g) * 
				 (#e_post == {{ "elem", #ename1, #n, #a1, #c1 }}) *
				 Grove(#alpha, #g2_post) * (#g2_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		pre:  [[ (n == #n) * DocumentNode(this, #l_e, #e, #l_g, #g) * 
				 (#e == {{ }}) *
				 Forest(#alpha, #g2) * (#g2 == {{ {{ "elem", #ename1, #n, #a1, #c1 }} }}) ]]
		post: [[ DocumentNode(this, #l_e, #e_post, #l_g, #g) * 
				 (#e_post == {{ "elem", #ename1, #n, #a1, #c1 }}) *
				 Forest(#alpha, #g2_post) * (#g2_post == {{ }}) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal

	@onlyspec hasChildNodes()
		pre:  [[ DocumentNode(this, #l_element, {{ "elem", #ename1, #n, #a1, #c1 }}, #l_grove, #grove) ]]
		post: [[ DocumentNode(this, #l_element, {{ "elem", #ename1, #n, #a1, #c1 }}, #l_grove, #grove) * (ret == $$t) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, {{ }}, #l_grove, #grove) ]]
		post: [[ DocumentNode(this, #l_element, {{ }}, #l_grove, #grove) * (ret == $$f) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
		(#children == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
		(#children == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) * (ret == $$t) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
		(#children == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
		(#children == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }}) * (ret == $$t) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) * (ret == $$f) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == $$f) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "hole", #gamma1 }}, {{ "text", #m, #t1 }}, {{ "hole", #gamma2 }} }})]]
		post: [[ AttributeNode(#name, this, #l_children, {{ }}) * (ret == $$t) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, {{ }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, {{ }}) * (ret == $$f) ]]
		outcome: normal

*/ /*
	----Document Node Axioms----
*/ /*
	@onlyspec documentElement()
		pre:  [[ DocumentNode(this, #l_element, {{ "elem", #ename1, #n, #a1, #c1 }}, #l_grove, #grove) ]]
		post: [[ DocumentNode(this, #l_element, {{ "elem", #ename1, #n, #a1, #c1 }}, #l_grove, #grove) * (ret == #n) * types(#n : $$object_type) ]]
		outcome: normal;
		
		pre:  [[ DocumentNode(this, #l_element, $$nil, #l_grove, #grove) ]]
		post: [[ DocumentNode(this, #l_element, $$nil, #l_grove, #grove) * (ret == $$null) ]]
		outcome: normal

	@onlyspec createElement(s)
		pre:  [[ (s == #name) *  DocumentNode(this, #l_element, #element, #l_g, #g) ]]
		post: [[ (ret == #en) * DocumentNode(this, #l_element, #element, #l_g, ({{ {{ "elem", #name, #en, {{}}, {{}} }} }} @ #g)) * types(#en : $$object_type) ]]
		outcome: normal

	@onlyspec createTextNode(s)
		pre:  [[ (s == #text)  * DocumentNode(this, #l_element, #element, #l_g, #g) ]]
		post: [[ (ret == #tn) * DocumentNode(this, #l_element, #element, #l_g, ({{ {{ "text", #tn, #text }} }} @ #g)) * types(#tn : $$object_type) ]]
		outcome: normal

	@onlyspec createAttribute(s)
		pre:  [[ (s == #name) *  DocumentNode(this, #l_element, #element, #l_g, #g) ]]
		post: [[ (ret == #en) * DocumentNode(this, #l_element, #element, #l_g, ({{ {{ "attr", #name, #an, #tf }} }} @ #g)) * types(#an : $$object_type) ]]
		outcome: normal

*/ /*
	----Element Node Axioms----
*/ /*

	@onlyspec tagName()
		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (ret == #name) * types(#name : $$string_type) ]]
		outcome: normal

	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * val(#t, #s1) ]]
		post: [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * 
				 (ret == #s1) * types(#s1 : $$string_type) ]]
		outcome: normal;
		
		pre:  [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * out(#attr, #s) ]]
		post: [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (ret == "")    ]]
		outcome: normal
	
	@onlyspec setAttribute(s, v)
		pre:  [[ (s == #s1) * (v == #s2) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #m, #t }}, {{ "hole", #alpha }} }}) * Grove(#g_alpha, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #m, #t2 }}, {{ "hole", #alpha }} }}) * 
				 (#t2 == {{ {{ "text", #r, #s2 }} }}) * Grove(#g_alpha, {{ #t }}) ]]
		outcome: normal;

		pre:  [[ (s == #s1) * (v == #s2) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 out(#attr, #s1) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr2, #l_children, #children) * 
				 (#attr2 == {{ "attr", #s1, #m, #t }} :: #attr) * (#t == {{ {{ "text", #r, #s2 }} }}) ]]
		outcome: normal

	@onlyspec removeAttribute(s)
		pre:  [[ (s == #s1) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #m, #t }}, {{ "hole", #alpha }} }}) * Grove(#g_alpha, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "hole", #alpha }} }}) * Grove(#g_alpha, {{ {{ "attr", #s1, #m, #t }} }}) ]]
		outcome: normal;
	
		pre:  [[ (s == #s1) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 out(#attr, #s1) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) ]]
		outcome: normal

	@onlyspec getAttributeNode(s)
		pre:  [[ (s == #s1) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #m, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #m, #t }}, {{ "hole", #alpha }} }}) * (ret == #m) * types(#m : $$object_type)]]
		outcome: normal;

		pre:  [[ (s == #s1) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * out(#attr, #s1) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (ret == $$null) ]]
		outcome: normal

	@onlyspec setAttributeNode(a)
		pre:  [[ (a == #m) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #p, #t1 }}, {{ "hole", #alpha1 }} }}) * Grove(#alpha2, {{ {{ "attr", #s1, #m, #t2 }} }}) * Grove(#alpha3, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #m, #t2 }}, {{ "hole", #alpha1 }} }}) * Grove(#alpha2, {{  }}) * Grove(#alpha3, {{ {{ "attr", #s1, #p, #t1 }} }}) *
				 (ret == #m) * types(#m : $$object_type) ]]
		outcome: normal;

		pre:  [[ (a == #m) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * Grove(#alpha, {{ {{ "attr", #s1, #m, #t1 }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, ({{ {{ "attr", #s1, #m, #t1 }} }} @ #attr), #l_children, #children) * Grove(#alpha, {{  }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec removeAttributeNode(a)
		pre:  [[ (a == #m) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "attr", #s1, #m, #t1 }}, {{ "hole", #alpha1 }} }}) * Grove(#alpha2, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * 
				 (#attr == {{ {{ "hole", #alpha1 }} }}) * Grove(#alpha2, {{ {{ "attr", #s1, #m, #t1 }} }}) * (ret == #m) * types(#m : $$object_type) ]]
		outcome: normal

*/

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
		(#e_chld_post == {{ {{ "hole", #alpha }}, {{ "text", #n, #t1 }} }}) *
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