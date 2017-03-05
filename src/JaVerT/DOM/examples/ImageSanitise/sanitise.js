/**
	@onlyspec isBlackListed() :
		pre: [[ scope(url: #s1) * scope(isB: #ignore) * isB(#s1) ]]
		post: [[ scope(url: #s1) * scope(isB:1) * isB(#s1) ]]
		outcome: normal;
		pre: [[ scope(url: #s1) * scope(isB: #ignore) * (not isB(#s1)) ]]
		post: [[ scope(url: #s1) * scope(isB:0) * (not isB(#s1)) ]]
		outcome: normal;		
*/

/**
	@id sanitise
	@rec false

	@pre (
		scope(img: #n) * 
		scope(cat: #s2) * 
		scope(cache: #c) *
		scope(url: #ignore1) * 
		scope(isB: #ignore2) *
		ElementNode(#n, #name, #attr, #children) *
		(#attr = #attr1 @ #a) *
		AttributeNode(#a, "src", {{#t}}) *
		TextNode(#t, #s1) *
		((#c, #t) -> 0) *
		isB(#s1)
	)
	@post (
		scope(img: #n) * 
		scope(cat: #s2) * 
		scope(cache: #c) *
		scope(url: #s1) * 
		scope(isB: 1) * 
		ElementNode(#n, #name, #new_attr, #children) *
		(#new_attr = #attr1 @ #a) *
		AttributeNode(#a, "src", {{#tn}}) *
		TextNode(#tn, #s2) *
		((#c, #t) -> 1) *
		isB(#s1)
	)
**/

function sanitiseImg(img, cat){
	var url = img.getAttribute("src");
	if(url){
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