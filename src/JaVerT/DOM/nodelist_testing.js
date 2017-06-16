/** adBlocker assertions */
/**
	@pred isB(s) : isB(s);
	@pred nisB(s) : nisB(s);

	@pred sanitised(t, i):
		(i == -1) * (t == {{ }}),
		(t == (#head :: #tail)) * (i == #i) * 
			isText(#head, #id, #t) * 
			(#j == (#i - 1)) * sanitised(#tail, #j),
		(t == (#head :: #tail)) * (i == #i) * 
			isElement(#head, #name, #id, #aList, #cList, #fin, #fout) * 
			sanitisedAS(#aList) * (#j == (#i - 1)) * sanitised(#tail, #j);

	@pred sanitisedAS(as):
		(as == {{ }}),
		(as == (#head :: #tail)) * isAttr(#head, #name, #id, #aList) * 
			(!(#name == "img")) * sanitisedAS(#tail),
		(as == (#head :: #tail)) * isAttr(#head, "img", #id, #aList) * 
			val(#aList, #s) * nisB(#s) * sanitisedAS(#tail);

	@onlyspec isBlackListed(s)
		pre:  [[ (s == #s) * isB(#s) ]]
		post: [[ isB(#s) * (ret == 1) ]]
		outcome: normal;
		pre:  [[ (s == #s) * (nisB(#s)) ]]
		post: [[ (ret == 0) * (nisB(#s)) ]]
		outcome: normal
*/

/*	@id sanitise
	@rec true

	@pre (
		InitialDOMHeap() *
		scope(cat: #s2) * nisB(#s2) * (f == #f) * (i == #i) * (len == #l) * (#i <# #l) * 
		ECell(#beta, #enname, #en, #enl_aList, #enaList, #enl_cList, #encList, #enfin, #enfout) *
		tids(#encList, #tid_l) * (#f --e-- #enfin) * (l-nth(#tid_l) == #n) *
		ECell(#alpha, #nname, #n, #nl_aList, #naList, #nl_cList, #ncList, #nfin, #nfout) *
		(#naList == #a1 @ ({{ "hole", #gamma }} :: #a2)) * (l-len(#a1) == #i) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * isB(#s1) * types(#s1 : $$string_type) * (! (#s1 == "")) *
		Grove(#grove, #g) *
		sanitisedAS(#a1)
	)
	@post (
		InitialDOMHeap() *
		scope(cat: #s2) * nisB(#s2) *
		ECell(#beta, #enname, #en, #enl_aList, #enaList, #enl_cList, #encList, #enfin, #enfout) *
		tids(#encList, #tid_l) * (#f --e-- #enfin) *
		ECell(#alpha, #nname, #n, #nl_aList, #naList_post, #nl_cList, #ncList, #nfin, #nfout) *
		(#naList_post == #a1 @ ({{ "attr", "src", #a, #tf2 }} :: #a2) ) *
		(#tf2 == {{ {{ "hole", #gamma3 }} }}) *
		TCell(#gamma3, #r, #s2) * nisB(#s2) *
		sanitisedAS({{ "attr", "src", #a, #tf2 }} :: #a1) *
		true
	)
*/
function sanitise(f, i, len) {
	if (i < len) {
		/* @callspec unfoldFL(#any1, #n, #f) */
		n = f.item(i);
		/* @callspec foldFL(#any2, #n, #f) */
		if (n.nodeType() == 1) {
			sanitiseImg(n, cat);
		}
		/* @unfold AttributeNode("src", #a, #l_tf, #tf2) */
		/* @callspec deallocTF(#any3, #l_tf, #gamma3) */
		/* @fold AttributeNode("src", #a, #l_tf, #tf2) */
		/* @fold val(#tf2, #s2) */
		0;
		/* @unfold ElementNode(#nname, #n, #nl_aList, #naList, #nl_cList, #ncList, #nfin, #nfout) */
		/* @callspec deallocF(#any4, #nl_cList, #gamma) */
		/* @fold ElementNode(#nname, #n, #nl_aList, #naList, #nl_cList, #ncList, #nfin, #nfout) */
		/* @fold sanitisedAS({{ "attr", "src", #a, #tf2 }} :: #a1) */
		0;
	}
}

/**
	@id sanitiseImg

	@pre (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		InitialDOMHeap() * (img == #n) * (cat == #s2) * nisB(#s2) *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children, #fin, #fout) *
		out(#attr, "src")
	)
	@post (
		InitialDOMHeap() * nisB(#s2) *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children, #fin, #fout)
	)
	@pre (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		InitialDOMHeap() * (img == #n) * (cat == #s2) * nisB(#s2) *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children, #fin, #fout) *
		(#attr == #a1 @ ({{ "hole", #gamma }} :: #a2)) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * isB(#s1) * types(#s1 : $$string_type) * (! (#s1 == "")) *
		Grove(#grove, #g) 
	)
	@post (
		InitialDOMHeap() *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children, #fin, #fout) *
		(#attr == #a1 @ ({{ "hole", #gamma }} :: #a2)) *
		ACell(#gamma, "src", #a, #l_tf, #tf2) *
		(#tf2 == {{ {{ "hole", #gamma3 }} }}) *
		TCell(#gamma3, #r, #s2) * nisB(#s2) *
		isB(#s1) * true
	)
	@pre (
		scope(isBlackListed: #isB_fun) * fun_obj(isBlackListed, #isB_fun, #isB_proto) *
		InitialDOMHeap() *
		(img == #n) * (cat == #s2) * nisB(#s2) *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children, #fin, #fout) *
		(#attr == #a1 @ ({{ "hole", #gamma }} :: #a2)) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * nisB(#s1) * types(#s1 : $$string_type) * (! (#s1 == ""))
	)
	@post (
		InitialDOMHeap() * nisB(#s2) *
		ECell(#alpha, #name, #n, #l_attr, #attr, #l_children, #children, #fin, #fout) *
		ACell(#gamma, "src", #a, #l_tf, #tf1) *
		val(#tf1, #s1) * nisB(#s1)
	)
**/
function sanitiseImg(img, cat){
	var url = img.getAttribute("src");
	if(url !== ""){
		var isB = isBlackListed(url);
		if(isB){
			img.setAttribute("src", cat);
		}	
	}
}