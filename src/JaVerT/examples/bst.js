/**

	@pred nullableObject(o) : 
		types(o : $$object_type),
		(o == $$null) * types (o : $$null_type);

	@pred Node(n, val, left, right) :
		standardObject(n)            *
		dataField(n, "value", val)   * types(val : $$number_type) *
		dataField(n, "left",  left)  * nullableObject(left)       *
		dataField(n, "right", right) * nullableObject(right);

	@pred BST(n, K) :
		(n == $$null) * (K == -{ }-) * types (n : $$null_type, K : $$set_type),
		Node(n, #val, #left, #right) * BST(#left, #KL) * BST(#right, #KR) * 
		(K == (#KL -u- -{ #val }- -u- #KR)) *
		types(#val : $$number_type, K : $$set_type, #KL : $$set_type, #KR : $$set_type);
		
	@lemma
		BST($$null, #x) ==> (#x == -{ }-) * types (#x : $$set_type)
*/

/**
	@pre
		BST($$null, #x)

	@post
		(#x == -{ }-) * types (#x : $$set_type)
*/
function lemma ()
{
	/** @unfold BST($$null, #x) */
	return true
}

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
		(t == #t) * BST(#t, #K) * types(#t : $$object_type) *
		(v == #v) * types (#v : $$number_type) *
		scope(make_node : #makeNode) * fun_obj(makeNode, #makeNode, #mknProto) *
		scope(insert : #insert) * fun_obj(insert, #insert, #insertProto)
		
	@post 
		BST(#t, #K -u- -{ #v }-) * (ret == #t) *
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

  /** @fold BST(#t, #K -u- -{ #v }-) */
  return t;
}