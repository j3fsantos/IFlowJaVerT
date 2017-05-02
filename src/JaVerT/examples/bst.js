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
		Node(n, #val, #left, #right) * BST(#left) * BST(#right);
		
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
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #whatever)
		
	@post 
		BST(#r) * types (#r : $$object_type) * (ret == #r) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #whatever)
		
		
	@pre
		(t == #t) * BST(#t) * types (#t : $$object_type) *
		(v == #v) * types (#v : $$number_type) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mkn_proto) *
		scope(insert: #insert) * fun_obj(insert, #insert, #ins_proto)
		
	@post 
		BST(#t) * (ret == #t) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #whatever_alpha) *
		scope(insert: #insert) * fun_obj(insert, #insert, #ins_proto)
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

function find (v, t)
{
  if (t === null)
    return false;
  else if (v === t.value)
    return true;
  else if (v < t.value)
    return find(v, t.left);
  else
    return find(v, t.right);
}

function find_min(t)
{
  if (t.left === null)
    return t.value;
  else
    return find_min(t.left);
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

  return t;
}