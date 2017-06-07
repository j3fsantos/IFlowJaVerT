/**
	@pred nullableObject(o) : 
		types(o : $$object_type),
		(o == $$null) * types (o : $$null_type);

	@pred Node(n, val, height, left, right) :
		standardObject(n) *
		dataField(n, "value", val) * dataField(n, "height", height) * dataField(n, "left",  left) * dataField(n, "right", right) *
		types(val : $$number_type, height : $$number_type);

	@pred AVL(n, K, h) :
		(n == $$null) * (K == -{ }-) * (h == 0) * types (n : $$null_type, K : $$set_type, h : $$number_type),
		
		Node(n, #val, h, #left, #right) * AVL(#left, #KL, #hl) * AVL(#right, #KR, #hr) * 
		(K == -u- (#KL, -{ #val }-, #KR)) * 
		(0 <# h) * (h == #hr + 1) * (#hl - #hr == -1) * 
		(forall #x : $$number_type. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : $$number_type. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#val : $$number_type, K : $$set_type, #KL : $$set_type, #KR : $$set_type, #hl : $$number_type, #hr : $$number_type),
		
		Node(n, #val, h, #left, #right) * AVL(#left, #KL, #hlr) * AVL(#right, #KR, #hlr) * 
		(K == -u- (#KL, -{ #val }-, #KR)) * 
		(h == #hlr + 1) * 
		(forall #x : $$number_type. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : $$number_type. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#val : $$number_type, K : $$set_type, #KL : $$set_type, #KR : $$set_type, #hlr : $$number_type),

		Node(n, #val, h, #left, #right) * AVL(#left, #KL, #hl) * AVL(#right, #KR, #hr) * 
		(K == -u- (#KL, -{ #val }-, #KR)) * 
		(h == #hl + 1) * (#hl - #hr == 1) * 
		(forall #x : $$number_type. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : $$number_type. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#val : $$number_type, K : $$set_type, #KL : $$set_type, #KR : $$set_type, #hl : $$number_type, #hr : $$number_type);
*/

/**
	@id makeNode
	
	@pre 
		(v == #v) * types (#v : $$number_type)
		
	@post
		Node(#r, #v, 1, $$null, $$null) * types (#r : $$object_type) * (ret == #r)
*/
function make_node(v)
{
  var node = {
    value  : v,
    height : 1,
    left   : null,
    right  : null
  };
  return node;
}

/**
	@id height
	
	@pre  (t == $$null) 
	@post (ret == 0)
		
	@pre
		(t == #t) * types(#t : $$object_type) *
		standardObject(#t) * dataField(#t, "height", #hgt) * types(#hgt : $$number_type)
	
	@post
		standardObject(#t) * dataField(#t, "height", #hgt) * (ret == #hgt)
*/
function height(t)
{
	var result = t ? t.height : 0;
	
	return result
}

/**
	@id max
	
	@pre  (a == #a) * (b == #b) * types (#a : $$number_type, #b : $$number_type) * (a <# b)
	@post (ret == #b)
		
	@pre  (a == #a) * (b == #b) * types (#a : $$number_type, #b : $$number_type) * (b <=# a)
	@post (ret == #a)
*/
function max(a, b)
{
  return a > b ? a : b;
}

// Balancing tree

function left_rotate(x)
{
  var y;

  y = x.right;
  x.right = y.left;
  y.left = x;

  x.height = max(height(x.left), height(x.right)) + 1;
  y.height = max(height(y.left), height(y.right)) + 1;

  return y;
}

function right_rotate(x)
{
  var y;

  y = x.left;
  x.left = y.right;
  y.right = x;

  x.height = max(height(x.left), height(x.right)) + 1;
  y.height = max(height(y.left), height(y.right)) + 1;

  return y;
}

/**
	@id balance
	
	@pre 
		(t == #t) * 
		Node(#t, #val, #h, #left, #right) * AVL(#left, #KL, #hl) * AVL(#right, #KR, #hr) * 
		(0 <# h) * (#h == #hr + 1) * ((#hl - #hr == -1) \/ (#hl - #hr == -1) \/ (#hl - #hr == 1)) * 
		(forall #x : $$number_type. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : $$number_type. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#KL : $$set_type, #KR : $$set_type, #hl : $$number_type, #hr : $$number_type) *
		scope(height : #height) * fun_obj(height, #height, #heightProto) *
		scope(max : #max) * fun_obj(max, #max, #maxProto)
	@post
		AVL(#t, #K_new, #h) * (#K_new == -u- (#KL, -{ #val }-, #KR)) *
		scope(height : #height) * fun_obj(height, #height, #heightProto) *
		scope(max : #max) * fun_obj(max, #max, #maxProto)
*/
function balance(t)
{
  /** 
  	@unfold AVL(#left, #KL, #hl)
  	@unfold AVL(#right, #KR, #hr)
  */
  if (height(t.left) - height(t.right) === 2) {
    if (height(t.left.left) < height(t.left.right))
      t.left = left_rotate(t.left);
    t = right_rotate(t);
  }
  else if (height(t.left) - height(t.right) === -2) {
    if (height(t.right.left) > height(t.right.right))
      t.right = right_rotate(t.right);
    t = left_rotate(t);
  }

  t.height = max(height(t.left), height(t.right)) + 1;
  /** 
  	@invariant dataField(#t, "left", #lnew) * dataField(#t, "right", #rnew) 
  	@fold AVL(#lnew, #KL_new, #hl)
  	@fold AVL(#rnew, #KR_new, #hr)
  	@fold AVL(#t, -u- (#KL, -{ #val }-, #KR), #h_new)
  */
  return t;
}

