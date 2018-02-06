/**

  @pred nullableObject(o) : 
    types(o : Obj),
    (o == null);

 @pred Node(n:Obj, v:Num, t):
   JSObject(n) *
   DataProp(n, "value", v) *
   DataProp(n, "next", t);
 
 @pred NDList(l, E):
   (l == null) * (E == -{ }-),

   Node(l, #v, #t) * NDList(#t, #tE) *
   (E == -u- (#tE, -{ #v }-)) *
   (!(#v --e-- #tE));

 @pred SOList(l, E):
   (l == null) * (E == -{ }-),

   Node(l, #v, #t) * SOList(#t, #tE) *
   (E == -u- (#tE, -{ #v }-)) *
   (forall #x: Num. ((! (#x --e-- #tE)) \/ (#v <# #x)));
   
 */
 
/**
	@id insert

	@pre ( initialHeapPostWeak() * (node == #n) * (value == #v) * SOList(#n, #E) * types(#v: Num) * 
		 scope(insert: #insert_fun) * JSFunctionObject(#insert_fun, "insert", #insert_sc, #insert_len, #insert_proto))
	@post ( initialHeapPostWeak() * (ret == #ret) * SOList(#ret, -u- (-{ #v }-, #E)) * types(#ret: Obj) *
		 scope(insert: #insert_fun) * JSFunctionObject(#insert_fun, "insert", #insert_sc, #insert_len, #insert_proto))
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
    
    /** @tactic assert(scope(result : #res)) 
        @tactic fold SOList(#res, -u- (-{ #v }-, #E)) */
    return result;
}

/**
	@id sort

	@pre (initialHeapPostWeak() * (head == #h) * NDList(#h, #E) * 
		  scope(sort: #sort_fun) * JSFunctionObject(#sort_fun, "sort", #sort_sc, #sort_len, #sort_proto) * 
		  scope(insert: #insert_fun) * JSFunctionObject(#insert_fun, "insert", #insert_sc, #insert_len, #insert_proto))
	@post (initialHeapPostWeak() * SOList(ret, #E) * nullableObject(ret) * 
		  scope(sort: #sort_fun) * JSFunctionObject(#sort_fun, "sort", #sort_sc, #sort_len, #sort_proto) * 
		  scope(insert: #insert_fun) * JSFunctionObject(#insert_fun, "insert", #insert_sc, #insert_len, #insert_proto))
*/
function sort(head) {
    var result;
    /** @tactic unfold NDList(#h, #E) */
    if (head === null) {
        /** @tactic fold SOList(null, -{ }-) */
        result = null
    } else {
        var rec = sort(head.next);
        result = insert(rec, head.value)
    }
    return result;
}

