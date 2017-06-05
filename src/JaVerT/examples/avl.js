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
		(h == #hr + 1) * (#hl - #hr == -1) * 
		(forall #x : $$number_type. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : $$number_type. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#val : $$number_type, K : $$set_type, #KL : $$set_type, #KR : $$set_type, #hl : $$number_type, #hr : $$number_type),
		
		Node(n, #val, h, #left, #right) * AVL(#left, #KL, #hlr) * AVL(#right, #KR, #hlr) * 
		(K == -u- (#KL, -{ #val }-, #KR)) * 
		(h == #hlr + 1) * 
		(forall #x : $$number_type. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : $$number_type. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#val : $$number_type, K : $$set_type, #KL : $$set_type, #KR : $$set_type, #hl : $$number_type, #hr : $$number_type),

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
	@id findMin
	
	@pre
		(t == #t) * AVL(#t, #K, #h) * types(#t : $$object_type, #h : $$number_type) * 
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)

	@post 
		AVL(#t, #K, #h) * (ret == #r) * types(#r : $$number_type) * (#r --e-- #K) * 
		(forall #x : $$number_type. ((! (#x --e-- #K)) \/ (#r <=# #x))) *
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)
*/
function find_min(t)
{
	/** @unfold AVL(#t, #K, #h) */
	var result;
	
	/** @invariant dataField(#t, "left", #il) * AVL(#il, #KL, #hl) 
	 	@flash AVL(#il, #KL, #hl) */
	if (t.left === null)
		result = t.value;
	else
		result = find_min(t.left);
		
	/** @fold AVL(#t, #K, #h) */
	return result;
}

/**
	@id find
	
	@pre
		(t == #t) * AVL(#t, #K, #h) * (v == #v) * types (#v : $$number_type) * 
		scope(find : #find) * fun_obj(find, #find, #findProto)

	@post 
		AVL(#t, #K, #h) * (ret == (#v -e- #K)) * types(#r : $$boolean_type) *
		scope(find : #find) * fun_obj(find, #find, #findProto)
*/
function find (v, t)
{
	var result;

	/** @unfold AVL(#t, #K, #h) */	
	if (t === null)
		result = false;
	else if (v === t.value)
		result = true;
	else {
		if (v < t.value)
		  result = find(v, t.left) 
		else
		  result = find(v, t.right);
	}
	
	/** @fold AVL(#t, #K, #h) */
	return result;
}

function max(a, b)
{
  return a > b ? a : b;
}

function height(t)
{
  return t ? t.height : 0;
}

function update_height(t)
{
  t.height = max(height(t.left), height(t.right)) + 1;
}

// Balancing tree

function left_rotate(x)
{
  var y;

  y = x.right;
  x.right = y.left;
  y.left = x;

  update_height(x);
  update_height(y);

  return y;
}

function right_rotate(x)
{
  var y;

  y = x.left;
  x.left = y.right;
  y.right = x;

  update_height(x);
  update_height(y);

  return y;
}

function balance(t)
{
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

  return t;
}


// Tree operations


function insert(v, t)
{
  if (t === null)
    return make_node(v);

  if (v < t.value)
    t.left = insert(v, t.left);
  else if (v > t.value)
    t.right = insert(v, t.right);
  else
    return t;

  update_height(t);
  t = balance(t);

  return t;
}

function remove(v, t)
{
  if (t === null)
    return null;

  if (v === t.value) {
    if (t.left === null) {
      return t.right;
    }
    else if (t.right === null) {
      return t.left;
    }
    else {
      var min = find_min(t.right);
      t.right = remove(min, t.right);
      t.value = min;
    }
  }
  else if (v < t.value)
    t.left = remove(v, t.left);
  else
    t.right = remove(v, t.right);

  update_height(t);
  t = balance(t);

  return t;
}
