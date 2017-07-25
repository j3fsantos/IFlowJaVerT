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
  dataField(node, "next", next);

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
  dataField(node, "head", head) *
  dataField(node, "last_next", last_next) *
  ll_seg(head, last_next, list);

@pred dll_obj(obj, head, head_prev, last, last_next, list):
  types(list: $$list_type) *
  standardObject(obj) *
  dataField(node, "head", head) *
  dataField(node, "head_prev", head_prev) *
  dataField(node, "last", last) *
  dataField(node, "last_next", last_next) *
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

    head.next = new_dll_seg_obj.head;

    return_obj.r_last = new_dll_seg_obj.last;

    /* Remove references to the uwanted object, so it is no longer part of our heap */
    new_dll_seg_obj = null;

    /** @tactic fold dll_seg(#head, #head_prev, #last, #last_next, #list) */

    return return_obj;

  }
}

/** The wrapper function is in another file while I am debugging this one */
