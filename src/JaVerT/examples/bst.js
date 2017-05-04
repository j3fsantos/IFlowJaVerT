/**

	@pred nullableObject(o) : 
		types(o : $$object_type),
		(o == $$null) * types (o : $$null_type);

	@pred Node(n, val, left, right) :
		standardObject(n)            *
		dataField(n, "value", val)   * types(val : $$number_type) *
		dataField(n, "left",  left)  * nullableObject(left)       *
		dataField(n, "right", right) * nullableObject(right);

	@pred BST(n) :
		(n == $$null) * types (n : $$null_type),
		Node(n, #val, #left, #right) * BST(#left) * BST(#right) * 
		types(#val : $$number_type);
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
		(t == #t) * BST(#t) * (#t == $$null) *
		(v == #v) * types (#v : $$number_type) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)
		
	@post 
		BST(#r) * types (#r : $$object_type) * (ret == #r) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)


	@pre
		(t == #t) * BST(#t) * types(#t : $$object_type) *
		(v == #v) * types (#v : $$number_type) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)
		
	@post 
		BST(#t) * (ret == #t) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)
*/
function insert(v, t)
{
  var result;
  
  /** @unfold BST(#t) */
  if (t === null) {
  
  	result = make_node(v);
  	
  	/** @invariant scope(result : #r) 
  		@fold BST($$null)
  		@fold BST($$null)
  		@fold BST(#r) */
    return result
  }

  if (v < t.value)
    t.left = insert(v, t.left);
  else if (v > t.value) 
    t.right = insert(v, t.right);

  /** @fold BST(#t) */
  return t;
}

/**
	@id find
	
	@pre
		(t == #t) * BST(#t) * (v == #v) * types (#v : $$number_type) * 
		scope(find : #find) * fun_obj(find, #find, #findProto)

	@post 
		BST(#t) * (ret == #r) * types(#r : $$boolean_type) *
		scope(find : #find) * fun_obj(find, #find, #findProto)
*/
function find (v, t)
{
	var result;

	/** @unfold BST(#t) */
	if (t === null)
		/** @fold BST(#t) */
		return false;
	else if (v === t.value)
		/** @fold BST(#t) */
		return true;
	else {
		if (v < t.value)
		  result = find(v, t.left) 
		else
		  result = find(v, t.right);

		/** @fold BST(#t) */
		return result;
	}
}

/**
	@id findMin
	
	@pre
		(t == #t) * BST(#t) * types (#t : $$object_type) * 
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)

	@post 
		BST(#t) * (ret == #r) * types(#r : $$number_type) *
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)
*/
function find_min(t)
{
	var result;
	
	/** @unfold BST(#t) */
	if (t.left === null)
		result = t.value;
	else
		result = find_min(t.left);
		
	/** @fold BST(#t) */
	return result;
}

/**
	@id remove
	
	@pre
		(t == #t) * BST(#t) * (v == #v) * types (#v : $$number_type) * nullableObject(#t) *
		scope(remove : #remove) * fun_obj(remove, #remove, #removeProto) *
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)

	@post 
		(ret == #r) * BST(#r) * nullableObject(#r) *
		scope(remove : #remove) * fun_obj(remove, #remove, #removeProto) *
		scope(find_min : #findMin) * fun_obj(findMin, #findMin, #findMinProto)
*/
function remove(v, t)
{
	/** @unfold BST(#t) */
	if (t === null)
		/** @fold BST(#t) */
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

	/** @fold BST(#t) */
  	return t;
}