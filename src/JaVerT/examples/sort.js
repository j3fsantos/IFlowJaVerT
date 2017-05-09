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

 @pre (node == #n) * (value == #v) * SOList(#n, #E)
 @post ( (ret == #ret) * SOList(#ret, -u- (-{ #v }-, #E)) * types(#ret: $$object_type) )
 */
function insert(node, value) {
    var result;
    /** @unfold SOList(#n, #E) */
    if (node === null) {
        result = { next: null, value: value }
        /** @invariant scope(result: #res)
            @fold SOList($$null, -{ }-)
            @fold SOList(#res, -{ #v }-) */
    } else if (node.value == value) {
        // Let's be defensive
        result = node;
    } else if (node.value < value) {
        var rec = insert(node.next, value);
        /** @invariant scope(rec: #rec)
            @unfold SOList(#rec, #rE)
            @fold SOList(#rec, #rE) */
        result = { next: rec, value: node.value }
        /** @invariant scope(result: #res)
            @fold SOList(#res, -u- (-{ #v }-, #rE)) */
    } else {
        result = { next: node, value: value }
        /** @invariant scope(result: #res)
            @unfold SOList(#n, #nE)
            @fold SOList(#n, #nE)
            @fold SOList(#res, -u- (-{ #v }-, #nE)) */
    }
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
        result = null
        /** @fold SOList($$null, -{ }-) */
    } else {
        var rec = sort(head.next);
        result = insert(rec, head.value)
    }
    return result;
}

