/**

  @pred nullableObject(o) : 
    types(o : $$object_type),
    (o == $$null) * types (o : $$null_type);

 @pred Node(n, v, t):
   standardObject(n) *
   dataField(n, "value", v) *
   dataField(n, "next", t) *
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
		 scope(insert: #insert_fun) * fun_obj(insert, #insert_fun, #insert_proto))
	@post ( (ret == #ret) * SOList(#ret, -u- (-{ #v }-, #E)) * types(#ret: $$object_type) *
		 scope(insert: #insert_fun) * fun_obj(insert, #insert_fun, #insert_proto) )
*/
function insert(node, value) {
    
    var result;

    /** @unfold SOList(#n, #E) */
    if (node === null) {
    	/** @fold SOList(#n, #E) */
        result = { next: null, value: value }
    } else if (node.value === value) {
        result = node;
    } else if (node.value < value) {
        var rec = insert(node.next, value);
        /** @flash SOList(#rec, #rE) */
        result = { next: rec, value: node.value }
    } else {
        result = { next: node, value: value }
    }
    
    /** @invariant scope(result : #res) 
        @fold SOList(#res, -u- (-{ #v }-, #E)) */
    return result;
}

/**
	@id sort

	@pre ((head == #h) * NDList(#h, #E) * 
		  scope(sort: #sort_fun) * fun_obj(sort, #sort_fun, #sort_proto) * 
		  scope(insert: #insert_fun) * fun_obj(insert, #insert_fun, #insert_proto))
	@post (SOList(ret, #E) * nullableObject(ret) * 
		  scope(sort: #sort_fun) * fun_obj(sort, #sort_fun, #sort_proto) * 
		  scope(insert: #insert_fun) * fun_obj(insert, #insert_fun, #insert_proto))
*/
function sort(head) {
    var result;
    /** @unfold NDList(#h, #E) */
    if (head === null) {
        /** @fold SOList($$null, -{ }-) */
        result = null
    } else {
        var rec = sort(head.next);
        result = insert(rec, head.value)
    }
    return result;
}
