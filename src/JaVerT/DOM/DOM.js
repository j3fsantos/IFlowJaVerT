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

	@pred AttributeNode(name, an, l_children, children) :
		DOMObject(an, $l_anp) *
		((an, "@name") -> name) *
		((an, "@children") -> l_children) * TextForest(l_children, children) *
		types(name: $$string_type, children: $$list_type) *
		empty_fields(an : "@proto", "@class", "@extensible", "@name", "@children");

	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();
		
	@pred DocumentElement(l, element) :
		isEmpty(element) * DOMObject(l, $$null) *
		empty_fields(l : "@proto", "@class", "@extensible"),
		
		isElement(element, #id, #name, #aList, #cList) * DOMObject(l, $$null) *
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * empty_fields(l : "@proto", "@class", "@extensible"),
	    
	    isHole(element, #alpha) * DOMObject(l, $$null) *
	    empty_fields(l : "@proto", "@class", "@extensible");		

	@pred AttributeSet(l, attrs) : 
	    isEmpty(attrs) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
	    
	    (attrs == (#head :: #attrsNext)) * isAttr(#head, #name, #id, #tf) * DOMObject(l, $$null) * 
	    ((l, "@next") -> #next) * AttributeNode(#name, #id, #l_tf, #tf) * AttributeSet(#next, #attrsNext) * 
	    empty_fields(l : "@proto", "@class", "@extensible", "@next"); 	

	@pred Forest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextNode(#id, #text) * Forest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@next"),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #aList, #cList) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * Forest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@next"),
		
	    (childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@next") -> #next) * Forest(#next, #childListNext) *
	    empty_fields(l : "@proto", "@class", "@extensible", "@next");

	
	@pred TextForest(l, childList) :
		isEmpty(childList) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextNode(#id, #text) * TextForest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@next"),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextForest(#next, #childListNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@next");
	
	@pred Grove(l, content) :
		isEmpty(content) * DOMObject(l, $$null) * ((l, "@next") ->  $$null),
		
		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * TextNode(#id, #text) * Grove(#next, contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@next"),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #aList, #cList) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) * Grove(#next, #contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@next"),	
		
		(content == (#head :: #contentNext)) * isAttr(head, #name, #id, #tList) * DOMObject(l, $$null) *
		((l, "@next") -> #next) * AttributeNode(#name, #id, #l_tf, #tList) * Grove(#next, #contentNext) *
		empty_fields(l : "@proto", "@class", "@extensible", "@next"),	
			
	    (content == (#head :: #contentNext)) * isHole(#head, #alpha) * DOMObject(l, $$null) *
	    ((l, "@next") -> #next) * Grove(#next, #contentNext) *
	    empty_fields(l : "@proto", "@class", "@extensible", "@next");

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
		post: [[ Grove(#l, (#g1 @ ({{"hole", #alpha}} @ #g3))) * Grove(#alpha, {{#g2}}) * (ret == #alpha) * types(#alpha : $$object_type)]]
		outcome: normal

	@onlyspec deallocG(alpha)
		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{"hole", #alpha}} @ #g3)) * Grove(#alpha, #g2)]]
		post: [[ Grove(#dn, (#g1 @ (#g2 @ #g3))) ]]
		outcome: normal


	@onlyspec createElement(x)
		pre:  [[ (x == #name) *  DocumentNode(this, #l_element, #element, #g) ]]
		post: [[ (ret == #ret) * DocumentNode(this, #l_element, #element, ({{ {{ "elem", #name, #ret, {{}}, {{}} }} }} @ #g)) * types(#ret : $$object_type) ]]
		outcome: normal

	@onlyspec createTextNode(x)
		pre:  [[ (x == #text)  * DocumentNode(this, #l_element, #element, #g) ]]
		post: [[ (ret == #ret) * DocumentNode(this, #l_element, #element, ({{ {{ "text", #ret, #text }} }} @ #g)) * types(#ret : $$object_type) ]]
		outcome: normal

	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * val(#t, #s1) ]]
		post: [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#attr == {{ {{ "attr", #s, #m, #t }}, {{ "hole", #alpha }} }}) * (ret == #s1) * types(#s1 : $$string_type) ]]
		outcome: normal;
		
		pre:  [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * out(#attr, #s) ]]
		post: [[ (s == #s) * ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (ret == "")    ]]
		outcome: normal


	@onlyspec nodeName()
		pre:  [[ DocumentNode(this, #l_element, #element, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (ret == "#document")]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (ret == #name) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == "#text") ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == #name) ]]
		outcome: normal

	@onlyspec nodeValue()
		pre:  [[ DocumentNode(this, #l_element, #element, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (ret == $$null) ]]
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
		pre:  [[ DocumentNode(#dn, #l_element, #element, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) ]]
		post: [[ DocumentNode(#dn, #l_element, #element, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) * (ret == #dn) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha2 }} }}) ]]
		post: [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha2 }} }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "text", this, #t }}, {{ "hole", #alpha2 }} }}) ]]
		post: [[ ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha1 }}, {{ "text", this, #t }}, {{ "hole", #alpha2 }} }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, #an, #l_children, #children) * (#children == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ AttributeNode(#name, #an, #l_children, #children) * (#children == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) * (ret == #an) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, #element, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha1 }} }}) ]]
		post: [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "elem", #name, this, #attrs, #children }}, {{ "hole", #alpha1 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "text", this, #t }}, {{ "hole", #alpha1 }} }}) ]]
		post: [[ Grove(#alpha, #nodes) * (#nodes == {{ {{ "text", this, #t }}, {{ "hole", #alpha1 }} }}) * (ret == $$null) ]]
		outcome: normal


	@onlyspec firstChild()
		pre:  [[ DocumentNode(this, #l_element, #element, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, {{ }}, #grove) ]]
		post: [[ DocumentNode(this, #l_element, {{ }}, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "hole", #alpha }} }}) * (ret == #en) ]]
		outcome: normal;
		
		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "text", #tn, #t }}, {{ "hole", #alpha }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, {{ }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec lastChild()
		pre:  [[ DocumentNode(this, #l_element, #element, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (#element == {{ "elem", #name, #en, #attrs, #children }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, {{ }}, #grove) ]]
		post: [[ DocumentNode(this, #l_element, {{ }}, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) * (ret == #en) ]]
		outcome: normal;
		
		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) ]]
		post: [[ ElementNode(#name, this, #l_attr, #attr, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ TextNode(this, #text) ]]
		post: [[ TextNode(this, #text) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", #tn, #t }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, this, #l_children, {{ }}) ]]
		post: [[ AttributeNode(#name, this, #l_children, {{ }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec previousSibling()
		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t }}, {{ "elem", #name, this, #en_attr, #en_children }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t }}, {{ "elem", #name, this, #en_attr, #en_children }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "text", this, #t }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, #en, #en_attr, #en_children }}, {{ "text", this, #t }} }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, #en, #a1, #c1 }}, {{ "elem", #n2, this, #a2, #c2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, #en, #a1, #c1 }}, {{ "elem", #n2, this, #a2, #c2 }} }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t1 }}, {{ "text", this, #t2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t1 }}, {{ "text", this, #t2 }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "text", this, #t1 }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "text", this, #t1 }}, {{ "hole", #alpha }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "hole", #alpha }} }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "hole", #alpha }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(#dn, #l_element, #element, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) ]]
		post: [[ DocumentNode(#dn, #l_element, #element, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, #element, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (ret == $$null) ]]
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
		post: [[ TextForest(#alpha, #f) * (#f == {{ {{ "text", #tn, #t1 }}, {{ "text", this, #t2 }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) ]]
		post: [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "text", this, #t }}, {{ "hole", #alpha }} }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec nextSibling()
		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t }}, {{ "elem", #name, #en, #en_attr, #en_children }} }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, this, #en_attr, #en_children }}, {{ "text", #tn, #t }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #name, this, #en_attr, #en_children }}, {{ "text", #tn, #t }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "elem", #n2, #en, #a2, #c2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "elem", #n1, this, #a1, #c1 }}, {{ "elem", #n2, #en, #a2, #c2 }} }}) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t1 }}, {{ "text", #tn, #t2 }} }}) ]]
		post: [[ Forest(#alpha, #f) * (#f == {{ {{ "text", this, #t1 }}, {{ "text", #tn, #t2 }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", this, #t1 }} }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "text", this, #t1 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #n1, this, #a1, #c1 }}  }}) ]]
		post: [[ ElementNode(#name, #en, #l, #a, #l_children, #children) * (#children == {{ {{ "hole", #alpha }}, {{ "elem", #n1, this, #a1, #c1 }} }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(#dn, #l_element, #element, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) ]]
		post: [[ DocumentNode(#dn, #l_element, #element, #grove) * (#element == {{ "elem", #name, this, #attrs, #children }}) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, #element, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (ret == $$null) ]]
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
		post: [[ TextForest(#alpha, #f) * (#f == {{ {{ "text", this, #t1 }}, {{ "text", #tn, #t2 }} }}) * (ret == #tn) ]]
		outcome: normal;

		pre:  [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "hole", #alpha }}, {{ "text", this, #t }} }}) ]]
		post: [[ AttributeNode(#name, #an, #l_tf, #tf) * (#tf == {{ {{ "hole", #alpha }}, {{ "text", this, #t }} }}) * (ret == $$null) ]]
		outcome: normal

	@onlyspec ownerDocument()
		pre:  [[ DocumentNode(this, #l_element, #element, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #grove) * (ret == $$null) ]]
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
		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #el, #ea, #el, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "elem", #ename2, #n, #a2, #c1 }} }}) * complete(#c1) ]]
		post: [[ ElementNode(#ename, this, #el, #ea, #el, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename2, #n, #a2, #c1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Grove(#alpha, #g) * (#g == {{ {{ "hole", #zeta }} }}) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (m == #m) * (n == #n) * ElementNode(#ename, this, #el, #ea, #el, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "elem", #ename2, #n, #a2, #c1 }} }}) * complete(#c1) ]]
		post: [[ ElementNode(#ename, this, #el, #ea, #el, #ec) * 
				 (#ec == {{ {{ "hole", #gamma1 }}, {{ "elem", #ename2, #n, #a2, #c1 }}, {{ "elem", #ename1, #m, #a1, #c1 }}, {{ "hole", #gamma2 }} }}) *
				 Forest(#alpha, #f) * (#f == {{ {{ "hole", #zeta }} }}) * (ret == #n) ]]
		outcome: normal
*/

/**
	@id groveParent
	@rec false

	TODO: complete spec
	
	@pre (
		scope(allocG   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocG : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() *
		(s == #s) *
		scope(document : $l_document) * types(#s : $$string_type, #grove: $$list_type) * 
		DocumentNode($l_document, #l_element, {{ }}, #grove)
	)
	@post (
		fun_obj(allocG,   #allocG,   #allocG_proto) *
		fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() *
		scope(document : $l_document) * types(#t : $$object_type) *
		DocumentNode($l_document, #l_element, {{ }}, ({{ {{ "text", #t, #s }} }} @ #grove))
	)
*/
function groveParent(s) {
	var t = document.createTextNode(s);
}