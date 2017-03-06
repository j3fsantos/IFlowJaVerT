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
		#attr == {("hole", #alpha):("attr", #a, "src", #tf1)} *
		#tf1 == {("hole", #t_alpha1):("text", #t, #s1)} *
		Grove(#l_g, #g1) *
		#g1 = {("hole", #g_alpha)} *
		((#c, #s1) -> 0) *
		isB(#s1)
	)
	@post (
		scope(img: #n) * 
		scope(cat: #s2) * 
		scope(cache: #c) *
		scope(url: #s1) * 
		scope(isB: 1) * 
		ElementNode(#n, #name, #new_attr, #children) *
		(#new_attr == {("hole", #alpha):("attr", #a, "src", #tf2)}) *
		(#tf2 == {("text", #r, #s2)}) *
		Grove(#l_g, #g2) *
		#g2 = {("hole", #g_alpha):#tf1} *
		((#c, #s1) -> 1) *
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