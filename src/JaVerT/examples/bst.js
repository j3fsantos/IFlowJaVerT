/**
	@pred NullableObject(o) : 
		types(o : $$object_type),
		(o == $$null) * types (o : $$null_type);

	@pred Node(n, val, left, right) :
		JSObject(n) *
		DataProp(n, "value", val) * DataProp(n, "left",  left) * DataProp(n, "right", right) *
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
		initialHeapPostWeak() * 
		(t == #t) * BST(#t, #K) * 
		(v == #v) * types (#v : $$number_type) *
		scope(make_node : #makeNode) * FunctionObject(#makeNode, "makeNode", _, _) *
		scope(insert : #insert) * FunctionObject(#insert, "insert", _, _)
		
	@post 
		initialHeapPostWeak() * 
		BST(#t_new, -u- (#K, -{ #v }-)) * (ret == #t_new) * types (#t_new : $$object_type) *
		scope(make_node : #makeNode) * FunctionObject(#makeNode, "makeNode", _, _) *
		scope(insert : #insert) * FunctionObject(#insert, "insert", _, _)
*/
function insert(v, t)
{
  var result;
  
  /** @tactic unfold BST(#t, #K) */
  if (t === null) {
  
  	result = make_node(v);
  	
  	/** @tactic assert (scope(result : #r))
  		@tactic fold BST($$null, -{ }-)
  		@tactic fold BST($$null, -{ }-)
  		@tactic fold BST(#r, -{ #v }-) */
    return result
  }

  if (v < t.value)
    t.left = insert(v, t.left);
  else if (v > t.value) 
    t.right = insert(v, t.right);

  /** @tactic fold BST(#t, -u- (#K, -{ #v }-)) */
  return t;
}

/**
	@id find
	
	@pre
		initialHeapPostWeak() *
		(t == #t) * BST(#t, #K) * (v == #v) * types (#v : $$number_type) * 
		scope(find : #find) * FunctionObject(#find, "find", _, _)

	@post 
		initialHeapPostWeak() * 
		BST(#t, #K) * (ret == (#v -e- #K)) * types(#r : $$boolean_type) *
		scope(find : #find) * FunctionObject(#find, "find", _, _)
*/
function find (v, t)
{
	var result;

	/** @tactic unfold BST(#t, #K) */	
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
	
	/** @tactic fold BST(#t, #K) */
	return result;
}

/**
	@id findMin
	
	@pre
		initialHeapPostWeak() * 
		(t == #t) * BST(#t, #K) * types(#t : $$object_type) * 
		scope(find_min : #findMin) * FunctionObject(#findMin, "findMin", _, _)

	@post 
		initialHeapPostWeak() * 
		BST(#t, #K) * (ret == #r) * types(#r : $$number_type) * (#r --e-- #K) * 
		(forall #x : $$number_type. ((! (#x --e-- #K)) \/ (#r <=# #x))) *
		scope(find_min : #findMin) * FunctionObject(#findMin, "findMin", _, _)
*/
function find_min(t)
{
	/** @tactic unfold BST(#t, #K) */
	var result;
		
	/** @tactic assert (DataProp(#t, "left", #il) * BST(#il, #KL)) 
	    @tactic flash BST(#il, #KL) */
	if (t.left === null)
		result = t.value;
	else
		result = find_min(t.left);
		
	/** @tactic fold BST(#t, #K) */
	return result;
}

/**
	@id remove
		
	@pre
		initialHeapPostWeak() * 
		(t == #t) * BST(#t, #K) * 
		(v == #v) * types (#v : $$number_type) *
		scope(remove : #remove) * FunctionObject(#remove, "remove", _, _) *
		scope(find_min : #findMin) * FunctionObject(#findMin, "findMin", _, _)

	@post 
		initialHeapPostWeak() * 
		(ret == #t_new) * BST(#t_new, #K_new) * (#K_new == #K -d- -{ #v }-) * NullableObject(#t_new) *
		scope(remove : #remove) * FunctionObject(#remove, "remove", _, _) *
		scope(find_min : #findMin) * FunctionObject(#findMin, "findMin", _, _)
*/
function remove(v, t)
{
	/** @tactic unfold BST(#t, #K) */
	if (t === null)
		/** @tactic fold BST(#t, #K) */
		return null;

	/** @tactic assert(DataProp(#t, "left", #il) * DataProp(#t, "right", #ir) * BST(#il, #KL) * BST(#ir, #KR)) */
	if (v === t.value) {
		/** @tactic flash BST(#il, #KL) */
		if (t.left === null) {	
				/** @tactic flash BST(#ir, #KR) */
				return t.right;
			}
		else 
		/** @tactic flash BST(#ir, #KR) */
		if (t.right === null) {
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

	/** @tactic fold BST(#t, #K -d- -{ #v }-) */
  	return t;
}