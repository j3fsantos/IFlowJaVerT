/**
	@pred Node(n, val, left, right) :
		standardObject(n) *
		dataField(n, "value", val) * dataField(n, "left",  left) * dataField(n, "right", right) *
		types(val : $$number_type);

	@pred BST(n, K) :
		(n == $$null) * (K == -{ }-) * types (n : $$null_type, K : $$set_type),
		
		Node(n, #val, #left, #right) * BST(#left, #KL) * BST(#right, #KR) * 
		(K == (#KL -u- -{ #val }- -u- #KR)) *
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
		BST(#t, #K -u- -{ #v }-) * (ret == #t) * types (#t : $$object_type) *
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

  /** @invariant dataField(#t, "value", #iv) * dataField(#t, "left", #il) * dataField(#t, "right", #ir) */

  /** @if (#il == $$null) {
           unfold BST(#il, #il_set); 
           fold BST(#il, #il_set)
       } 
  **/
  /** @if (#ir == $$null) {
           unfold BST(#ir, #ir_set); 
           fold BST(#ir, #ir_set)
       } 
  **/
  if (v < t.value)
    t.left = insert(v, t.left);
  else if (v > t.value) 
    t.right = insert(v, t.right);

  /** @fold BST(#t, #K -u- -{ #v }-) */
  return t;
}