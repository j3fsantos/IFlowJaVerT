/**
	@pred nullableObject(o) : 
		types(o : $$object_type),
		(o == $$null) * types (o : $$null_type);

	@pred Node(n, val, left, right) :
		standardObject(n) *
		dataField(n, "value", val) * dataField(n, "left",  left) * dataField(n, "right", right) *
		types(val : $$number_type);

	@pred BST(n, K) :
		(n == $$null) * (K == -{ }-) * types (n : $$null_type, K : $$set_type),
		
		Node(n, #val, #left, #right) * BST(#left, #KL) * BST(#right, #KR) * 
		(K == -u- (#KL, -{ #val }-, #KR)) * 
		(forall #x : $$number_type. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : $$number_type. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#val : $$number_type, K : $$set_type, #KL : $$set_type, #KR : $$set_type);
*/

/**
	@id makeNode
	
	@pre 
		(v == #v) * types (#v : $$number_type)
		
	@post
		Node(#r, #v, $$null, $$null) * types (#r : $$object_type) * (ret == #r)
*/
function make_node(v)
{
  var node = {
    value : v,
    left  : null,
    right : null
  };
  return node;
}

/**
	@id insert

	@pre
		(t == #t) * BST(#t, #K) * (#t == $$null) * (#K == -{ }-) *
		(v == #v) * types (#v : $$number_type) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)
		
	@post 
		BST(#r, -{ #v }-) * types (#r : $$object_type) * (ret == #r) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)



	@pre
		(t == #t) * BST(#t, #K) * (! (#t == $$null)) *
		(v == #v) * types (#v : $$number_type) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)
		
	@post 
		BST(#t, -u- (#K, -{ #v }-)) * (ret == #t) * types (#t : $$object_type) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)
*/
function insert(v, t)
{
  var result;
  
  /** @unfold BST(#t, #K) */
  if (t === null) {
  
  	result = make_node(v);
  	
  	/** @invariant scope(result : #r) 
  		@fold BST($$null, -{ }-)
  		@fold BST($$null, -{ }-)
  		@fold BST(#r, -{ #v }-) */
    return result
  }

  if (v < t.value)
    t.left = insert(v, t.left);
  else if (v > t.value) 
    t.right = insert(v, t.right);

  /** @fold BST(#t, -u- (#K, -{ #v }-)) */
  return t;
}

/**
	@id find
	
	@pre
		(t == #t) * BST(#t, #K) * (v == #v) * (#v --e-- #K) * types (#v : $$number_type) * 
		scope(find : #find) * fun_obj(find, #find, #findProto)

	@post 
		BST(#t, #K) * (ret == $$t) * types(#r : $$boolean_type) *
		scope(find : #find) * fun_obj(find, #find, #findProto)

	@pre
		(t == #t) * BST(#t, #K) * (v == #v) * (! (#v --e-- #K)) * types (#v : $$number_type) * 
		scope(find : #find) * fun_obj(find, #find, #findProto)

	@post 
		BST(#t, #K) * (ret == $$f) * types(#r : $$boolean_type) *
		scope(find : #find) * fun_obj(find, #find, #findProto)
*/
function find (v, t)
{
	var result;

	/** @unfold BST(#t, #K) */	
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
	
	/** @fold BST(#t, #K) */
	return result;
}

/**
	@id findMin
	
	@pre
		(t == #t) * BST(#t, #K) * (! (#t == $$null)) * 
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)

	@post 
		BST(#t, #K) * (ret == #r) * types(#r : $$number_type) * (#r --e-- #K) *
		(forall #x : $$number_type. ((! (#x --e-- #K)) \/ (#r <=# #x))) *
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)
*/
function find_min(t)
{
	var result;
	
	/** @unfold BST(#t, #K) */
	if (t.left === null)
		/** @invariant dataField(#t, "left", #il) * BST(#il, #KL)
			@unfold BST(#il, #KL)
			@fold BST(#il, #KL)
		*/
		result = t.value;
	else
		result = find_min(t.left);
		
	/** @fold BST(#t, #K) */
	return result;
}

/**
	@id remove
		
	@pre
		(t == #t) * BST(#t, #K) * 
		(v == #v) * types (#v : $$number_type) *
		scope(remove : #remove) * fun_obj(remove, #remove, #removeProto) *
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)

	@post 
		(ret == #t_new) * BST(#t_new, #K_new) * nullableObject(#t_new) * (#K_new == #K -d- -{ #v }-) *
		scope(remove : #remove) * fun_obj(remove, #remove, #removeProto) *
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)
*/
function remove(v, t)
{
	/** @unfold BST(#t, #K) */
	if (t === null)
		/** @fold BST(#t, #K) */
		return null;

	/** @invariant dataField(#t, "left", #il) * dataField(#t, "right", #ir) *  BST(#il, #KL) * BST(#ir, #KR) */
	
	if (v === t.value) {
		if (t.left === null) {	
				/** @unfold BST($$null, #KL) */
				return t.right;
			}
		else 
		if (t.right === null) {
				/** @unfold BST($$null, #KR) */
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

	/** @fold BST(#t, #K -d- -{ #v }-) */
  	return t;
}