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

	@pred ENode(alpha, name, id, l_attr, aList, l_children, cList) :
		DOMObject(id, $l_enp) * ((id, "@address") -> alpha) * empty_fields(id : "@name", "@attributes", "@children", "@address") * 
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
		((l, "@next") -> next) * ((l, "@content") -> content);


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
		TextNode(#id, #text) *
		ChainCell(l, #next, #id) * ForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isElement(#head, #name, #id, #aList, #cList) * 
		DOMObject(#id, $l_enp) * empty_fields(#id : "@name", "@attributes", "@children") *
		ElementNode(#name, #id, #l_addr, #aList, #l_children, #cList) *
		ChainCell(l, #next, #id) * ForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * ForestRec(#next, #childListNext);


	@pred TextForest(alpha, childList) : 
		((alpha, "@chain") ->  #l) * TextForestRec(#l, childList);
	
	@pred TextForestRec(l, childList) :
		isNil(childList) * (l == $$null),

		(childList == (#head :: #childListNext)) * isText(#head, #id, #text) * 
		TextNode(#id, #text) *
		ChainCell(l, #next, #id) * TextForestRec(#next, #childListNext),
		
		(childList == (#head :: #childListNext)) * isHole(#head, #alpha) *
		ChainCell(l, #next, #alpha) * TextForestRec(#next, #childListNext);


	@pred Grove(alpha, content) : 
		((alpha, "@chain") ->  #l) * GroveRec(alpha, #l, content) * types(content : $$list_type, #l: $$object_type);	
	
	@pred GroveRec(root, l, content) :
		isNil(content) * ((l, "@address") -> root),

		(content == (#head :: #contentNext)) * isText(#head, #id, #text) * 
		TextNode(#id, #text) * ((l, "@address") -> root) *
		ChainCell(l, #next, #id) * GroveRec(#next, #contentNext),
		
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
			TextNode(id, text);

	@pred ACell(alpha, name, id, l_children, cList) : 
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, id) * 
		DOMObject(id, $l_anp) * ((id, "@address") -> alpha) * empty_fields(id : "@name", "@children", "@address") *
		AttributeNode(name, id, l_children, cList);	

	@pred EmptyCell(alpha) :
		((alpha, "@chain") ->  #l) * ChainCell(#l, $$null, $$null);





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



	@onlyspec allocF(l, i)
		pre:  [[ (l == #l) * (i == #i) * types(#g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Forest(#l, #g) * (#g == #g1 @ ( {{"elem", #name, #id, #aList, #cList}} :: #g2)) * (l-len(#g1) == #i) * types(#id : $$object_type) ]]
		post: [[ Forest(#l, #g_post) * (#g_post == (#g1 @ ({{ "hole", #alpha }} :: #g2))) *
				 ECell(#alpha, #name, #new_id, #l_attr, #aList, #l_children, #cList) * (ret == #alpha) * 
				 (#new_id == #id) * types(#alpha : $$object_type)]]
		outcome: normal;

		pre:  [[ (l == #l) * (i == #i) * types(#g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Forest(#l, #g) * (#g == #g1 @ ( {{"text", #id, #text}} :: #g2)) * (l-len(#g1) == #i) ]]
		post: [[ Forest(#l, #g_post) * (#g_post == (#g1 @ ({{ "hole", #alpha }} :: #g2))) *
				 TCell(#alpha, #id, #text) * (ret == #alpha) * types(#alpha : $$object_type)]]
		outcome: normal;

		pre:  [[ (l == #l) * (i == -1) * Forest(#l, #g) ]]
		post: [[ Forest(#l, #g_post) * (#g_post == ({{ "hole", #alpha }} :: #g)) * Forest(#alpha, {{ }}) * (ret == #alpha)]]
		outcome: normal

	@onlyspec deallocF(l, alpha)
		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Forest(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g3)) * Forest(#alpha, #g2) ]]
		post: [[ Forest(l, #g_post) * (#g_post == (#g1 @ (#g2 @ #g3))) * (ret == $$empty) ]]
		outcome: normal; 

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g3 : $$list_type) * 
				 Forest(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g3)) * EmptyCell(#alpha) ]]
		post: [[ Forest(l, #g_post) * (#g_post == (#g1 @ #g3)) * (ret == $$empty) ]]
		outcome: normal; 

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Forest(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * ECell(#alpha, #name, #id, #l_attr, #aList, #l_children, #cList) ]]
		post: [[ Forest(l, #g_post) * (#g_post == (#g1 @ ({{"elem", #name, #id, #aList, #cList}} :: #g2))) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Forest(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * TCell(#alpha, #id, #text) ]]
		post: [[ Forest(l, #g_post) * (#g_post == (#g1 @ ({{"text", #id, #text}} :: #g2))) * (ret == $$empty) ]]
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
		outcome: normal;

		pre:  [[ (l == #l) * (i == -1) * Grove(#l, #g) ]]
		post: [[ Grove(#l, #g_post) * (#g_post == ({{ "hole", #alpha }} :: #g)) * Grove(#alpha, {{ }}) * (ret == #alpha)]]
		outcome: normal

	@onlyspec deallocG(l, alpha)
		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type, #g3 : $$list_type) * 
				 Grove(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g3)) * Grove(#alpha, #g2) ]]
		post: [[ Grove(l, #g_post) * (#g_post == (#g1 @ (#g2 @ #g3))) * (ret == $$empty) ]]
		outcome: normal; 

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g3 : $$list_type) * 
				 Grove(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g3)) * EmptyCell(#alpha) ]]
		post: [[ Grove(l, #g_post) * (#g_post == (#g1 @ #g3)) * (ret == $$empty) ]]
		outcome: normal; 

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * ECell(#alpha, #name, #id, #l_attr, #aList, #l_children, #cList) ]]
		post: [[ Grove(l, #g_post) * (#g_post == (#g1 @ ({{"elem", #name, #id, #aList, #cList}} :: #g2))) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * TCell(#alpha, #id, #text) ]]
		post: [[ Grove(l, #g_post) * (#g_post == (#g1 @ ({{"text", #id, #text}} :: #g2))) * (ret == $$empty) ]]
		outcome: normal;

		pre:  [[ (alpha == #alpha) * types(#alpha : $$object_type, #g : $$list_type, #g1 : $$list_type, #g2 : $$list_type) * 
				 Grove(l, #g) * (#g == #g1 @ ({{ "hole", #alpha }} :: #g2)) * ACell(#alpha, #name, #id, #l_children, #cList) ]]
		post: [[ Grove(l, #g_post) * (#g_post == (#g1 @ ({{"attr", #name, #id, #cList}} :: #g2))) * (ret == $$empty) ]]
		outcome: normal

*/ /*
	----General Axioms----
*/ /*

	@onlyspec nodeName()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec nodeValue()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec nodeType()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec parentNode()
		pre:  [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ {{ "hole", #alpha }} }}) * 
				 ECell(#alpha, #name, this, #l_attr, #attr, #l_children, #children) ]]
		post: [[ DocumentNode(#dn, #l_element, #element, #l_g, #grove) * (#element == {{ {{ "hole", #alpha }} }}) * 
				 ECell(#alpha, #name, this, #l_attr, #attr, #l_children, #children) * (ret == #dn) ]]
		outcome: normal;

		pre:  [[ ECell(#alpha, #name, #en, #l_attr, #attr, #l_children, #children) * (#children == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 ECell(#gamma, #name2, this, #l_attr2, #attr2, #l_children2, #children2) * types(#a1: $$list_type, #a2: $$list_type) ]]
		post: [[ ECell(#alpha, #name, #en, #l_attr, #attr, #l_children, #children) * (#children == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 ECell(#gamma, #name2, this, #l_attr2, #attr2, #l_children2, #children2) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ ECell(#alpha, #name, #en, #l_attr, #attr, #l_children, #children) * (#children == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 TCell(#gamma, this, #t) * types(#a1: $$list_type, #a2: $$list_type) ]]
		post: [[ ECell(#alpha, #name, #en, #l_attr, #attr, #l_children, #children) * (#children == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 TCell(#gamma, this, #t) * (ret == #en) ]]
		outcome: normal;

		pre:  [[ ACell(#alpha, #name, #an, #l_children, #children) * (#children == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 TCell(#gamma, this, #t) * types(#a1: $$list_type, #a2: $$list_type) ]]
		post: [[ ACell(#alpha, #name, #an, #l_children, #children) * (#children == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 TCell(#gamma, this, #t) * (ret == #an) ]]
		outcome: normal;

		pre:  [[ DocumentNode(this, #l_element, #element, #l_g, #grove) ]]
		post: [[ DocumentNode(this, #l_element, #element, #l_g, #grove) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ACell(#alpha, #name, this, #l_children, #children) ]]
		post: [[ ACell(#alpha, #name, this, #l_children, #children) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#l_g, #nodes) * (#nodes == #a1 @ ({{ "hole", #alpha }} :: #a2)) * 
				 ECell(#alpha, #name, this, #l_a, #attrs, #l_c, #children) * types(#a1: $$list_type, #a2: $$list_type) ]]
		post: [[ Grove(#l_g, #nodes) * (#nodes == #a1 @ ({{ "hole", #alpha }} :: #a2)) * 
				 ECell(#alpha, #name, this, #l_a, #attrs, #l_c, #children) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ Grove(#l_g, #nodes) * (#nodes == #a1 @ ({{ "hole", #alpha }} :: #a2)) * 
				 TCell(#alpha, this, #t) * types(#a1: $$list_type, #a2: $$list_type) ]]
		post: [[ Grove(#l_g, #nodes) * (#nodes == #a1 @ ({{ "hole", #alpha }} :: #a2)) * 
				 TCell(#alpha, this, #t) * (ret == $$null) ]]
		outcome: normal

	@onlyspec childNodes()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec firstChild()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec lastChild()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec previousSibling()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec nextSibling()
		pre:  [[ emp ]]
		post: [[ emp ]]
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

	@onlyspec insertBefore()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec replaceChild()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec removeChild()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec appendChild(n)
		pre:  [[ (n == #n) * ECell(#xeta, #name, this, #l_attr, #aList, #l_children, #cList) *
				 ECell(#beta, #name2, #n, #l_attr2, #aList2, #l_children2, #cList2) * complete(#cList2) ]]
		post: [[ ECell(#xeta, #name, this, #l_attr, #aList, #l_children, #cList2_post ) * (#cList2_post == #cList @ {{ {{ "hole", #beta2 }} }}) *
				 ECell(#beta2, #name2, #n, #l_attr2, #aList2, #l_children2, #cList2) *
				 EmptyCell(#beta) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (n == #n) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) *
				 TCell(#beta, #n, #text) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList_post) * (#cList_post == #cList @ {{ {{ "hole", #beta2 }} }}) * 
				 TCell(#beta2, #n, #text) * EmptyCell(#beta) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (n == #n) * ACell(#alpha, #name, this, #l_children, #cList) *
				 TCell(#beta, #n, #text) ]]
		post: [[ ACell(#alpha, #name, this, #l_children, #cList_post) * (#cList_post == #cList @ {{ {{ "hole", #beta2 }} }}) * 
				 TCell(#beta2, #n, #text) * EmptyCell(#beta) * (ret == #n) ]]
		outcome: normal;

		pre:  [[ (n == #n) * DocumentNode($l_document, #l_elem, {{ }}, #l_grove, #gList) * (this == $l_document) * 
				 ECell(#alpha, #name, #n, #l_attr, #aList, #l_children, #cList) ]]
		post: [[ DocumentNode($l_document, #l_elem, {{ {{ "hole", #alpha2 }} }}, #l_grove, #gList) *
				 ECell(#alpha2, #name, #n, #l_attr, #aList, #l_children, #cList) * EmptyCell(#alpha) * (ret == #n) ]]
		outcome: normal

	@onlyspec hasChildNodes()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

*/ /*
	----Document Node Axioms----
*/ /*

	@onlyspec documentElement()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec createElement(s)
		pre:  [[ (s == #name) * DocumentNode(this, #l_element, #element, #l_g, #g) * types(#name : $$string_type, #g : $$list_type) ]]
		post: [[ (ret == #en) * DocumentNode(this, #l_element, #element, #l_g, #g_post) * (#g_post == {{ "hole", #alpha }} :: #g) * 
				 ECell(#alpha, #name, #en, #e_l_a, $$nil, #e_l_c, $$nil) * types(#en : $$object_type) ]]
		outcome: normal

	@onlyspec createTextNode(s)
		pre:  [[ (s == #text)  * DocumentNode(this, #l_element, #element, #l_g, #g) ]]
		post: [[ (ret == #tn) * DocumentNode(this, #l_element, #element, #l_g, #g_post) * (#g_post == ({{ "hole", #alpha }} :: #g)) * 
				 TCell(#alpha, #tn, #text) * types(#tn : $$object_type) ]]
		outcome: normal

	@onlyspec createAttribute(s)
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec getElementsByTagName(s)
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

*/ /*
	----Element Node Axioms----
*/ /*

	@onlyspec tagName()
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec getAttribute(s)
		pre:  [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) *
				 (#aList == #a1 @ ({{ "hole", #gamma }} :: #a2)) * ACell(#gamma, #s, #m, #l_t, #t) * val(#t, #s1) * types(#s1 : $$string_type) ]]
		post: [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * ACell(#gamma, #s, #m, #l_t, #t) * (ret == #s1) ]]
		outcome: normal;

		pre:  [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * out(#aList, #s) ]]
		post: [[ (s == #s) * ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * (ret == "")     ]]
		outcome: normal


	@onlyspec setAttribute(s, v)
		pre:  [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * (s == #s1) * (v == #s2) * 
				 (#aList == #a1 @ ({{ "hole", #gamma }} :: #a2)) * ACell(#gamma, #s1, #m, #l_t, #t) * Grove(#beta, {{}}) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList_post, #l_children, #cList) * (#aList_post == #a1 @ ({{ "hole", #gamma }} :: #a2)) * 
				 ACell(#gamma, #s1, #m, #l_t, {{ {{ "hole", #gamma2 }} }}) * TCell(#gamma2, #r, #s2) * Grove(#beta, #t) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ ECell(#alpha, #name, this, #l_attr, #aList, #l_children, #cList) * 
				 (s == #s1) * (v == #s2) * out(#aList, #s1) ]]
		post: [[ ECell(#alpha, #name, this, #l_attr, #aList_post, #l_children, #cList) * (#aList_post == {{ "hole", #gamma }} :: #aList) * 
				 ACell(#gamma, #s1, #m, #l_t, {{ {{ "hole", #gamma2 }} }}) * TCell(#gamma2, #r, #s2) * (ret == $$null) ]]
		outcome: normal

	@onlyspec removeAttribute(s)
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec getAttributeNode(s)
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec setAttributeNode(s)
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec removeAttributeNode(s)
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

	@onlyspec getElementsByTagName(s)
		pre:  [[ emp ]]
		post: [[ emp ]]
		outcome: normal

*/ /*
	----Text Node Axioms----
*/ /*
	@onlyspec data()
		pre:  [[ TCell(#alpha, this, #text) * types(#text : $$string_type) ]]
		post: [[ TCell(#alpha, this, #text) * (ret == #text) ]]
		outcome: normal

	@onlyspec length()
		pre:  [[ TCell(#alpha, this, #text) ]]
		post: [[ TCell(#alpha, this, #text) * (ret == s-len(#text)) ]]
		outcome: normal

	@onlyspec substringData(o, c)
		pre:  [[ (o == #l1) * (c == #l2) * TCell(#alpha, this, #text) * (#l1 == s-len(#s1)) * (#l2 == s-len(#s2)) * (#text == #s1 ++ (#s2 ++ #s3)) *
				 types(#text : $$string_type, #s1 : $$string_type, #s2 : $$string_type) ]]
		post: [[ TCell(#alpha, this, #text) * (ret == #s2) ]]
		outcome: normal;

		pre:  [[ (o == #l1) * (c == #l2) * TCell(#alpha, this, #text) * (#text == #s1 ++ #s2) * (#l1 == s-len(#s1)) * (s-len(#s2) <=# #l2) * 
				 types(#text : $$string_type, #s1 : $$string_type, #s2 : $$string_type) ]]
		post: [[ TCell(#alpha, this, #text) * (ret == #s2) ]]
		outcome: normal

	@onlyspec appendData(s)
		pre:  [[ (s == #s2) * TCell(#alpha, this, #text) ]]
		post: [[ TCell(#alpha, this, (#text ++ #s2)) * (ret == $$null) ]]
		outcome: normal

	@onlyspec insertData(o, s)
		pre:  [[ (o == #l1) * (s == #s3) * TCell(#alpha, this, (#s1 ++ #s2)) * (#l1 == s-len(#s1)) * types(#s1 : $$string_type, #s2 : $$string_type, #s3 : $$string_type) ]]
		post: [[ TCell(#alpha, this, (#s1 ++ #s3 ++ #s2)) * (ret == $$null) ]]
		outcome: normal

	@onlyspec deleteData(o, c)
		pre:  [[ (o == #l1) * (c == #l2) * TCell(#alpha, this, (#s1 ++ #s2 ++ #s3)) * (#l1 == s-len(#s1)) * (#l2 == s-len(#s2)) * 
				 types(#s1 : $$string_type, #s2 : $$string_type, #s3 : $$string_type) ]]
		post: [[ TCell(#alpha, this, (#s1 ++ #s2)) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ (o == #l1) * (c == #l2) * TCell(#alpha, this, (#s1 ++ #s2)) * (#l1 == s-len(#s1)) * (s-len(#s2) <=# #l2) * 
				 types(#s1 : $$string_type, #s2 : $$string_type) ]]
		post: [[ TCell(#alpha, this, #s1) * (ret == $$null) ]]
		outcome: normal

	@onlyspec replaceData(o, c, s)
		pre:  [[ (o == #l1) * (c == #l2) * (s == #ns) * TCell(#alpha, this, #text) * (#l1 == s-len(#s1)) * (#l2 == s-len(#s)) * (#text == #s1 ++ #s ++ #s2) ]]
		post: [[ TCell(#alpha, this, (#s1 ++ #ns ++ #s2)) * (ret == $$null) ]]
		outcome: normal;

		pre:  [[ (o == #l1) * (c == #l2) * (s == #ns) * TCell(#alpha, this, (#s1 ++ #s)) * (#l1 == s-len(#s1)) * (s-len(#s) <=# #s) * 
				 types(#s1 : $$string_type, #s : $$string_type, #ns : $$string_type) ]]
		post: [[ TCell(#alpha, this, (#s1 ++ #ns)) * (ret == $$null) ]]
		outcome: normal

	@onlyspec splitText(o)
		pre:  [[ (o == #l1) * Forest(#f, {{ {{ "hole", #alpha1 }} }}) * TCell(#alpha1, this, (#s1 ++ #s2)) * (#l1 == s-len(#s1)) *
				 types(#s1 : $$string_type, #s2 : $$string_type) ]]
		post: [[ Forest(#f, {{ {{ "hole", #alpha1 }}, {{ "hole", #alpha2 }} }}) * 
				 TCell(#alpha1, this, #s1) * TCell(#alpha2, #n, #s2) * (ret == $$null) ]]
		outcome: normal
*/

/*
	@id banana

	@pre (
		InitialDOMHeap() * (tnode == #tn) *
		TCell(#alpha, #tn, #text_pre) * (#text_pre == "abcdefghi")
	)
	@post (
		InitialDOMHeap() * (ret == 9) *
		TCell(#alpha, #tn, #text_post) * (#text_post == "abcabcghi")
	)
*/
function banana(tnode) {
	var l = tnode.length();
	var c = tnode.substringData(0, 3);
	tnode.replaceData(3, 3, c);
	return l
}