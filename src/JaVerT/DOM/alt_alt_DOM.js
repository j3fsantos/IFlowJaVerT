/*
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

	@pred ENode(name, id, l_attr, aList, l_children, cList) :
		DOMObject(id, $l_enp) * empty_fields(id : "@name", "@attributes", "@children") * 
		ElementNode(name, id, l_attr, aList, l_children, cList);

	@pred ElementNode(name, id, l_attr, aList, l_children, cList) :
		((id, "@name") -> name) *
		((id, "@attributes") -> l_attr) * AttributeSet(l_attr, aList) *
		((id, "@children") -> l_children) * Forest(l_children, cList) * 
		types(name: $$string_type, aList: $$list_type, cList: $$list_type); 

	@pred TextNode(id, text) :
		DOMObject(id, $l_tnp) *
		((id, "@text") -> text) *
		empty_fields(id : "@text");

	@pred ANode(name, id, l_children, cList) :
		DOMObject(id, $l_anp) * empty_fields(id : "@name", "@children") *
		AttributeNode(name, id, l_children, cList);

	@pred AttributeNode(name, id, l_children, cList) :
		((id, "@name") -> name) *
		((id, "@children") -> l_children) * TextForest(l_children, cList);






	@pred InitialDOMHeap() :
		NodePrototype() * DocumentNodePrototype() * ElementNodePrototype() * AttributeNodePrototype() * TextNodePrototype();

	@pred DocumentElement(l, element) :
		isNil(element) * DOMObject(l, $$null) * empty_fields(l :),
		
		(element == (#head :: {{}})) * isElement(#head, #id, #name, #l_a, #l_c) * 
		DOMObject(l, $$null) * empty_fields(l :),
		
		(element == (#head :: {{}})) * isHole(#head, #alpha) * DOMObject(l, $$null) * empty_fields(l :);		


	@pred ChainCell(l, next, content) : 
		((l, "@next") -> next) * ((l, "@content") -> content) * empty_fields(l: "@next", "@content");


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
		DOMObject(alpha, $$null) * ((alpha, "@chain") ->  #l) * empty_fields(alpha : "@chain") * ForestRec(#l, childList);

	@pred ForestRec(l, childList) :
		isNil(childList) * (l == $$null),

		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * 
		TextNode(#id, #text) *
		ChainCell(l, #next, #id) * ForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #aList, #cList) * 
		DOMObject(#id, $l_enp) * empty_fields(#id : "@name", "@attributes", "@children") *
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) *
		ChainCell(l, #next, #id) * ForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * ForestRec(#next, #childListNext);


	@pred TextForest(alpha, childList) : 
		((alpha, "@chain") ->  #l) * empty_fields(alpha : "@chain") * TextForestRec(#l, childList);
	
	@pred TextForestRec(l, childList) :
		isNil(childList) * (l == $$null),

		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * 
		TextNode(#id, #text) *
		ChainCell(l, #next, #id) * TextForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * TextForestRec(#next, #childListNext);


	@pred Grove(alpha, content) : 
		((alpha, "@chain") ->  #l) * empty_fields(alpha : "@chain") * GroveRec(#l, content) * types(content : $$list_type);	
	
	@pred GroveRec(l, content) :
		isNil(content) * (l == $$null),

		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * 
		TextNode(#id, #text) *
		ChainCell(l, #next, #id) * GroveRec(#next, #contentNext),
		
		(content == (#head :: #contentNext)) * isElement(#head, #name, #id, #aList, #cList) * 
		DOMObject(#id, $l_enp) * empty_fields(#id : "@name", "@attributes", "@children") *
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) *
		ChainCell(l, #next, #id) * GroveRec(#next, #contentNext),

		(content == (#head :: #contentNext)) * isAttr(#head, #name, #id, #tfList) * 
		DOMObject(#id, $l_anp) * empty_fields(#id : "@name", "@children") *
		AttributeNode(#name, #id, #l_tf, #tfList) * 
		ChainCell(l, #next, #id) * GroveRec(#next, #contentNext),
		
		(content == (#head :: #contentNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * GroveRec(#next, #contentNext);



	@pred ECell(alpha, name, id, l_attr, aList, l_children, cList) : 
		 ((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, id) * empty_fields(alpha : "@chain") * 
			ENode(name, id, l_attr, aList, l_children, cList);

	@pred TCell(alpha, id, text) : 
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, id) * empty_fields(alpha : "@chain") * 
			TextNode(id, text);

	@pred ACell(alpha, name, id, l_children, cList) : 
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, id) * empty_fields(alpha : "@chain") * 
			ANode(name, id, l_children, cList);	

	@pred EmptyCell(alpha) :
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, $$null) * empty_fields(alpha : "@chain");





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


	@onlyspec allocF(l, i)
		pre:  [[ (l == #l) * (i == #i) * types(#f : $$list_type, #f1 : $$list_type, #f2 : $$list_type) * 
				 Forest(#l, #f) * (#f == #f1 @ ( {{"elem", #name, #id, #aList, #cList}} :: #f2)) * (l-len(#f1) == #i)]]
		post: [[ Forest(#l, (#f1 @ ({{ "hole", #alpha }} :: #f3))) * 
				 ECell(#alpha, #name, #id, #l_attr, #aList, #l_children, #cList) * (ret == #alpha) * types(#alpha : $$object_type)]]
		outcome: normal;

		pre:  [[ (l == #l) * (i == #i) * types(#f : $$list_type, #f1 : $$list_type, #f2 : $$list_type) * 
				 Forest(#l, #f) * (#f == #f1 @ ( {{"text", #id, #text}} :: #f2)) * (l-len(#f1) == #i)]]
		post: [[ Forest(#l, (#f1 @ ({{ "hole", #alpha }} :: #f3))) * 
				 TCell(#alpha, #id, #text) * (ret == #alpha) * types(#alpha : $$object_type)]]
		outcome: normal


	@onlyspec deallocF(alpha)
		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #f : $$list_type, #f1 : $$list_type, #f2 : $$list_type, #f3 : $$list_type) * 
				 Forest(#l, #f) * (#f == #f1 @ ({{ "hole", #alpha }} :: #f3)) * Forest(#alpha, #f2) ]]
		post: [[ Forest(#l, (#f1 @ (#f2 @ #f3))) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #f : $$list_type, #f1 : $$list_type, #f3 : $$list_type) * 
				 Forest(#l, #f) * (#f == #f1 @ ({{ "hole", #alpha }} :: #f3)) * EmptyCell(#alpha) ]]
		post: [[ Forest(#l, (#f1 @ #f3)) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #f : $$list_type, #f1 : $$list_type, #f2 : $$list_type) * 
				 Forest(#l, #f) * (#f == #f1 @ ({{ "hole", #alpha }} :: #f2)) * ECell(#alpha, #name, #id, #l_attr, #aList, #l_children, #cList) ]]
		post: [[ Forest(#l, (#f1 @ ({{"elem", #name, #id, #aList, #cList}} :: #f2))) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #f : $$list_type, #f1 : $$list_type, #f2 : $$list_type) * 
				 Forest(#l, #f) * (#f == #f1 @ ({{ "hole", #alpha }} :: #f2)) * TCell(#alpha, #id, #text) ]]
		post: [[ Forest(#l, (#f1 @ ({{"text", #id, #text}} :: #f2))) * (ret == $$empty) ]]
		outcome: normal



	@onlyspec allocG(l, i)
		pre:  [[ (l == #l) * (i == #i) * types(#g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ( {{"elem", #name, #id, #aList, #cList}} :: #g2)) * (l-len(#g1) == #i) * types(#id : $$object_type) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ ({{ "hole", #alpha }} :: #g2))) *
				 ECell(#alpha, #name, #new_id, #l_attr, #aList, #l_children, #cList) * (ret == #alpha) * 
				 (#new_id == #id) * types(#alpha : $$object_type)]]
		outcome: normal;

		pre:  [[ (l == #l) * (i == #i) * types(#g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ( {{"text", #id, #text}} :: #g2)) * (l-len(#g1) == #i) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ ({{ "hole", #alpha }} :: #g2))) *
				 TCell(#alpha, #id, #text) * (ret == #alpha) * types(#alpha : $$object_type)]]
		outcome: normal;

		pre:  [[ (l == #l) * (i == #i) * types(#g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ( {{"attr", #name, #id, #cList}} :: #g2)) * (l-len(#g1) == #i) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ ({{ "hole", #alpha }} :: #g2))) *
				 ACell(#alpha, #name, #id, #l_children, #cList) * (ret == #alpha) * types(#alpha : $$object_type)]]
		outcome: normal

	@onlyspec deallocG(alpha)
		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g3)) * Grove(#alpha, #g2) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ (#g2 @ #g3))) * (ret == $$empty) ]]
		outcome: normal; 

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g3 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g3)) * EmptyCell(#alpha) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ #g3)) * (ret == $$empty) ]]
		outcome: normal; 

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * ECell(#alpha, #name, #id, #l_attr, #aList, #l_children, #cList) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ ({{"elem", #name, #id, #aList, #cList}} :: #g2))) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * TCell(#alpha, #id, #text) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ ({{"text", #id, #text}} :: #g2))) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(#l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * ACell(#alpha, #name, #id, #l_children, #cList) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == (#g1 @ ({{"attr", #name, #id, #cList}} :: #g2))) * (ret == $$empty) ]]
		outcome: normal

*/ /*
	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) *
				 (#aList == #a1 @ ({{ "attr", #s, #m, #t }} :: #a2)) * val(#t, #s1) * types(#s1 : $$string_type) ]]
		post: [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) *
				 (ret == #s1) ]]
		outcome: normal;
		
		pre:  [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * out(#aList, #s) ]]
		post: [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * (ret == "")    ]]
		outcome: normal

	@onlyspec setAttribute(s, v)
		pre:  [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * (s == #s1) * (v == #s2) * 
				 (#aList == #a1 @ ({{ "attr", #s, #m, #t }} :: #a2)) * 
				 Grove(#beta, {{}}) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList_post, #l_children, #cList) *
				 (#aList_post == #a1 @ ({{ "attr", #s, #m, {{ {{ "text", #r, #s2 }} }} }} :: #a2)) *
				 Grove(#beta, #t) ]]
		outcome: normal;

		pre:  [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * (s == #s1) * (v == #s2) * out(#aList, #s1) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList_post, #l_children, #cList) * (#aList_post == {{ "attr", #s1, #m, {{ {{ "text", #r, #s2 }} }}   }} :: #aList) ]]
		outcome: normal

	@onlyspec ownerDocument()
		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * (ret == $l_document) ]]
		outcome: normal;

		pre:  [[ TCell(#alpha, this, #text) ]]
		post: [[ TCell(#alpha, this, #text) * (ret == $l_document) ]]
		outcome: normal;

		pre:  [[ ACell(#alpha, #name, this, #l_children, #cList) ]]
		post: [[ ACell(#alpha, #name, this, #l_children, #cList) * (ret == $l_document) ]]
		outcome: normal

	@onlyspec createElement(s)
		pre:  [[ (s == #name) * DocumentNode(this, #l_element, #element, #l_g, #g) * types(#name : $$string_type, #g : $$list_type) ]]
		post: [[ (ret == #en) * DocumentNode(this, #l_element, #element, #l_g, #g_post) * (#g_post == {{ "elem", #name, #en, {{ }}, {{ }} }} :: #g) * types(#en : $$object_type) ]]
		outcome: normal

	@onlyspec appendChild(n)
		pre:  [[ (n == #n) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) *
				 ECell(#beta, #name2, #n, #l_attr2, #aList2, #l_children2, #cList2) * complete(#cList2) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList2_post ) * 
				 (#cList2_post == #cList @ {{ {{ "elem", #name2, #n, #aList2, #cList2 }} }}) * EmptyCell(#beta) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (n == #n) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) *
				 TCell(#beta, #n, #text) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList_post) * 
				 (#cList_post == #cList @ {{ {{ "text", #n, #text }} }}) * EmptyCell(#beta) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (n == #n) * ACell(#alpha, #name, this, #l_children, #cList) *
				 TCell(#beta, #n, #text) ]]
		post: [[ ACell(#alpha, #name, this, #l_children, #cList_post) * 
				 (#cList_post == #cList @ {{ {{ "text", #n, #text }} }}) * EmptyCell(#beta) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (n == #n) * DocumentNode($l_document, #l_elem, {{ }}, #l_grove, #gList) * (this == $l_document) * 
				 ECell(#alpha, #name, #n, #l_attr, #aList, #l_children, #cList) ]]
		post: [[ DocumentNode($l_document, #l_elem, {{ {{ "elem", #name, #n, #aList, #cList}} }}, #l_grove, #gList) *
				 EmptyCell(#alpha) * (ret == #n) ]]
		outcome: normal

*/

/**
	@id createNewAttribute
	@rec false

	@pre (
		scope(allocG   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocG : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() * (element == #id) * (grove == #l_gList) * types(#en : $$object_type) *
		DocumentNode($l_document, #l_elem, #elem, #l_gList, #gList) *
		ECell(#alpha, #name, #id, #l_aList1, #aList1, #l_cList1, #cList1)
	)
	@post (
		scope(allocG   : #allocG)   * fun_obj(allocG,   #allocG,   #allocG_proto) *
		scope(deallocG : #deallocG) * fun_obj(deallocG, #deallocG, #deallocG_proto) *
		InitialDOMHeap() * (ret == $$t) * 
		DocumentNode($l_document, #d_l_elem, #d_elem, #d_l_g, #d_g_post) *
		ECell(#alpha, #name, #id, #l_aList1, #aList1, #l_cList1, #cList_post) *
		(#cList_post == (#cList1 @ {{ {{ "elem", "test", #n_id, #n_l_aList, {{ }}, #n_l_cList, {{ }} }} }}))
	)
*/
function createNewAttribute(grove, element){
	var d = element.ownerDocument();
	var e = d.createElement("test");
	var a = allocG(grove, 0);
	/* @invariant 
		scope(a : #zeta) * scope(e : #e2) * 
		ECell(#zeta, #name2, #e2, #l_aList2, #aList2, #l_cList2, #cList2) */
	/* @fold complete(#cList2) */
	var n = element.appendChild(e);
	deallocG(a);
	return (n === e);
}