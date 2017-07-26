/**
@pred dll_node(node, val, next, prev) :
  standardObject(node) *
  dataField(node, "value", val) *
  dataField(node, "next", next) *
  dataField(node, "prev", prev);

@pred dll_seg(head, head_prev, last, last_next, list) :
  types(list: $$list_type) *
  (list == {{ }}) *
  (head_prev == last) *
  (head == last_next),

  (! (head == last_next)) *
  types(list: $$list_type) *
  (list == (#item :: #items)) *
  (dll_node(head, #item, #next, head_prev)) *
  (dll_seg(#next, head, last, last_next, #items));

@pred ll_node(node, val, next) :
  standardObject(node) *
  dataField(node, "value", val) *
  dataField(node, "next", next) *
  empty_fields(node : -{"value", "next"}-);

@pred ll_seg(head, last_next, list):
  types(list: $$list_type) *
  (list == {{ }}) *
  (head == last_next),

  (! (head == last_next)) *
  (list == (#item :: #items)) *
  types(list: $$list_type, #items: $$list_type) *
  (ll_node(head, #item, #head_next)) *
  (ll_seg(#head_next, last_next, #items));

@pred ll_obj(obj, head, last_next, list):
  types(list: $$list_type) *
  standardObject(obj) *
  dataField(obj, "head", head) *
  dataField(obj, "last_next", last_next) *
  ll_seg(head, last_next, list) *
  empty_fields(obj : -{"head", "last_next"}-);

@pred dll_obj(obj, head, head_prev, last, last_next, list):
  types(list: $$list_type) *
  standardObject(obj) *
  dataField(obj, "head", head) *
  dataField(obj, "head_prev", head_prev) *
  dataField(obj, "last", last) *
  dataField(obj, "last_next", last_next) *
  dll_seg(head, head_prev, last, last_next, list);
*/

/**
	@id llSegToDllSeg

	@pre
    (head == #head) * (last_next == #last_next) * (head_prev == #head_prev) *
    ll_seg(#head, #last_next, #list) *
    scope(ll_seg_to_dll_seg : #llSegToDllSeg) *
    fun_obj(llSegToDllSeg, #llSegToDllSeg, #llSegToDllSegProto)

	@post
    (ret == #ret) *
    standardObject(#ret) *
    dataField(#ret, "r_head", #head) *
    dataField(#ret, "r_last", #last) *
    dll_seg(#head, #head_prev, #last, #last_next, #list) *
    scope(ll_seg_to_dll_seg : #llSegToDllSeg) *
    fun_obj(llSegToDllSeg, #llSegToDllSeg, #llSegToDllSegProto)
*/
function ll_seg_to_dll_seg(head, head_prev, last_next)
{
  /** @tactic unfold ll_seg(#head, #last_next, #list) */

  var return_obj = {
    r_head : null, /** Tried to set this to head but it wouldn't work (not enough type information about head?) */
    r_last : null /** Is set later */
  };

  if (head === last_next) { /* Verified */

    return_obj.r_head = head;
    return_obj.r_last = head_prev;

    /** @tactic fold dll_seg(#head, #head_prev, #head_prev, #head, #list) */

    return return_obj;

  } else {

    return_obj.r_head = head;

    /** Set pointer of current head */
    /** Head is extensible as it satisfies the standardObject pred */
    head.prev = head_prev; /* THIS IS THROWING AN ERROR. "BAD" ASSIGNMENT? */
    /** Even throws an error when head_prev is replaced by a constant,
       so it's not a problem with the value of head_prev */

    /** Recurse */
    var new_dll_seg_obj = ll_seg_to_dll_seg(head.next, head, last_next);

    head.next = new_dll_seg_obj.r_head;

    return_obj.r_last = new_dll_seg_obj.r_last;

    /** @tactic fold dll_seg(#head, #head_prev, #last, #last_next, #list) */

    return return_obj;

  }
}

/**
	@id ll_obj_to_dll_obj

	@pre
    (obj == #obj) * ll_obj(obj, #head, #last_next, #list) *
    scope(ll_seg_to_dll_seg : #llSegToDllSeg) *
    fun_obj(llSegToDllSeg, #llSegToDllSeg, #llSegToDllSegProto)

	@post
    dll_obj(#obj, #head, #head_prev, #last, #last_next, #list) * (ret == #obj) *
    scope(ll_seg_to_dll_seg : #llSegToDllSeg) *
    fun_obj(llSegToDllSeg, #llSegToDllSeg, #llSegToDllSegProto)
*/
function ll_obj_to_dll_obj(obj)
{
  var init_head_prev = null; /** ??? */

  var dll_seg_obj   = ll_seg_to_dll_seg(obj.head, init_head_prev, obj.last_next);

  obj.head      = dll_seg_obj.r_head;
  obj.head_prev = init_head_prev;
  obj.last      = dll_seg_obj.r_last;

  return obj;
}
