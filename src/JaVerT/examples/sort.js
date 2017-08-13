/**

  @pred nullableObject(o) : 
    types(o : $$object_type),
    (o == $$null) * types (o : $$null_type);

 @pred Node(n, v, t):
   JSObject(n) *
   DataProp(n, "value", v) *
   DataProp(n, "next", t) *
   types(v: $$number_type);
 
 @pred NDList(l, E):
   (l == $$null) * (E == -{ }-),

   Node(l, #v, #t) * NDList(#t, #tE) *
   (E == -u- (#tE, -{ #v }-)) *
   (!(#v --e-- #tE)) *
   types(#v: $$number_type, E: $$set_type, #tE: $$set_type);

 @pred SOList(l, E):
   (l == $$null) * (E == -{ }-),

   Node(l, #v, #t) * SOList(#t, #tE) *
   (E == -u- (#tE, -{ #v }-)) *
   (forall #x: $$number_type. ((! (#x --e-- #tE)) \/ (#v <# #x))) *
   types(#v: $$number_type, E: $$set_type, #tE: $$set_type);
 */
 
/**
	@id insert

	@pre ((node == #n) * (value == #v) * SOList(#n, #E) * types(#v: $$number_type) * 
		 scope(insert: #insert_fun) * FunctionObject(insert, #insert_fun, #insert_proto))
	@post ( (ret == #ret) * SOList(#ret, -u- (-{ #v }-, #E)) * types(#ret: $$object_type) *
		 scope(insert: #insert_fun) * FunctionObject(insert, #insert_fun, #insert_proto) )
*/
function insert(node, value) {
    
    var result;

    /** @tactic unfold SOList(#n, #E) */
    if (node === null) {
    	/** @tactic fold SOList(#n, #E) */
        result = { next: null, value: value }
    } else if (node.value === value) {
        result = node;
    } else if (node.value < value) {
        var rec = insert(node.next, value);
        result = { next: rec, value: node.value }
    } else {
        result = { next: node, value: value }
    }
    
    /** @invariant scope(result : #res) 
        @tactic fold SOList(#res, -u- (-{ #v }-, #E)) */
    return result;
}

/**
	@id sort

	@pre ((head == #h) * NDList(#h, #E) * 
		  scope(sort: #sort_fun) * FunctionObject(sort, #sort_fun, #sort_proto) * 
		  scope(insert: #insert_fun) * FunctionObject(insert, #insert_fun, #insert_proto))
	@post (SOList(ret, #E) * nullableObject(ret) * 
		  scope(sort: #sort_fun) * FunctionObject(sort, #sort_fun, #sort_proto) * 
		  scope(insert: #insert_fun) * FunctionObject(insert, #insert_fun, #insert_proto))
*/
function sort(head) {
    var result;
    /** @tactic unfold NDList(#h, #E) */
    if (head === null) {
        /** @tactic fold SOList($$null, -{ }-) */
        result = null
    } else {
        var rec = sort(head.next);
        result = insert(rec, head.value)
    }
    return result;
}

