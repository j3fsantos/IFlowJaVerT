/**
	@id doubleGet
	@rec false

	@pre (
		scope(element: #en) *
		ElementNode(#name, #en, #attr, #children) *
		(#attr == {{ {{"attr", "src", #a0, #atf0}} :: {{"attr", "width", #a1, #atf1}} :: {{"attr", "height", #a2, #atf2}} :: {{ "hole", #a_alpha2 }} }})
	)
	@post (
		scope(element: #en) *
		ElementNode(#name, #en, #attr, #children) *
		(#attr == {{ {{ "hole", #a_alpha1 }} :: {{"attr", "width", #a1, #atf1}} :: {{"attr", "height", #a2, #atf2}} :: {{ "hole", #a_alpha2 }} }})
	)
*/
function doubleGet(element) {
	var a = allocAS(#attr, 0, 1);
	var w = element.getAttribute("width");
	deallocAS(a);
	/**
	b = allocAS(#attr, 1, 1);
	var h = element.getAttribute("height");
	deallocAS(b); 
	*/
}