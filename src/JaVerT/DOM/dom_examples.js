/**
	@onlyspec allocAS(l, i, j)
		pre:  [[ (l == #l) * (i == #i) * (j == #j) * 
		         AttributeSet(#l, #as) * (#as == #as1 @ (#as2 @ #as3)) * (l-len(#as1) == #i) * (l-len(#as2) == #j)]]
		post: [[ AttributeSet(#l, (#as1 @ ({{"hole", #alpha}} @ #as3))) * 
		         AttributeSet(#alpha, #as2) ]]
		outcome: normal;
	
		[[ (l == #l) * (i == #i) * AttributeSet(#l, #as) * (l-len(#as) <=# #i) ]]
		[[ AttributeSet(#l, ({{"hole", #alpha}} @ #as)) * AttributeSet(#alpha, {{}} ) ]]
		normal

	@onlyspec deallocAS(alpha)
		[[ (alpha == #alpha) * AttributeSet(#l, #as) * (#as == #as1 @ ({{"hole", #alpha}} @ #as3)) * AttributeSet(#alpha, #as2) ]]
		[[ AttributeSet(#l, (#as1 @ (#as2 @ #as3))) ]]
		normal
*/

/**
	@id doubleGet
	@rec false

	@pre (
		scope(element: #en) * scope(w : #w) *
		ElementNode(#name, #en, #lattr, #attr, #l_children, #children) *
		(#attr == {{ 
			{{ "attr", "src", #a0, #atf0 }} :: 
			{{ "attr", "width", #a1, #atf1 }} :: 
			{{ "attr", "height", #a2, #atf2 }} :: 
			{{ "hole", #a_alpha2 }} 
		}})
	)
	
	@post (
		scope(element: #en) * scope (w : #a1) *
		ElementNode(#name, #en, #l_attr, #attr, #l_children, #children) *
		(#attr == {{ 
			{{ "attr", "src", #a0, #atf0 }} :: 
			{{ "attr", "width", #a1, #atf1 }} :: 
			{{ "attr", "height", #a2, #atf2 }} :: 
			{{ "hole", #a_alpha2 }} 
		}}))
*/
function doubleGet(element) {
	var a = allocAS(#l_attr, 1, 3);
	var w = element.getAttribute("src");
	deallocAS(a);
}