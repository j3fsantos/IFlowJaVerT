/**
	scope(img: #img) *
	ElementNode(#img, #name, #attr, #children) *
	(#attr = {{ {{"attr", #a1, "width", #tf1}}, {{"attr", #a2, "src", #tf2}} }}) *
	Grove(#l_grove, #g) *
	...rest of what is needed in sanitiseImg...
*/

allocAS(#attr, 0, 1);

/**
	scope(img: #img) *
	ElementNode(#img, #name, #attr, #children) *
	(#attr = {{ {{"hole", #alpha}}, {{"attr", #a2, "src", #tf2}} }}) *
	AttributeSet(#alpha, {{"attr", #a1, "width", #tf1}}) *
	Grove(#l_grove, #g) *
	...

	#attr now fits what is expected by the function precondition.
*/

allocG(#l_grove, 0, 0);

/**
	scope(img: #img) *
	ElementNode(#img, #name, #attr, #children) *
	(#attr = {{ {{"hole", #alpha}}, {{"attr", #a2, "src", #tf2}} }}) *
	AttributeSet(#alpha, {{"attr", #a1, "width", #tf1}}) *
	Grove(#alpha2, {{}}) *
	Grove(#l_grove, {{{{"hole", #alpha2}}::#g}}) *
	...

	This particular grove alloc doesn't exist, and adding empty list like this may require a
	separate spec, rather than just adding j like other alloc specs.
*/

sanitiseImg(img, cat);

/**
	For dealloc we also need to carry around the context hole name, unless we can use a mechanism
	to deduce it somehow from the last alloc call.
*/
deallocG(#l_grove, #alpha2);
deallocAS(#attr, #alpha);