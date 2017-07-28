/**
@pred ll_node(node, val, next):
  standardObject(node) *
  dataField(node, "value", val) *
  dataField(node, "next", next);

@pred ll_seg(head, last_next, list):
  types(list: $$list_type) *
  (list == {{ }}) *
  (head == last_next),

  (! (head == last_next)) *
  (list == (#item :: #items )) *
  types(list: $$list_type, #items: $$list_type) *
  (ll_node(head, #item, #head_next)) *
  (ll_seg(#head_next, last_next, #items));

@pred disjoint_ll_seg(head, last_next, list, disjoint_element):
  types(list: $$list_type) *
  (list == {{ }}) * (! (head == disjoint_element)) *
  (head == last_next),

  (! (head == last_next)) * (! (head == disjoint_element)) *
  (list == (#item :: #items )) *
  types(list: $$list_type, #items: $$list_type) *
  (ll_node(head, #item, #head_next)) *
  (disjoint_ll_seg(#head_next, last_next, #items, disjoint_element));

@pred ll_obj(obj, head, last_next, list):
  types(list: $$list_type) *
  standardObject(obj) *
  dataField(obj, "head", head) *
  dataField(obj, "last_next", last_next) *
  ll_seg(head, last_next, list);
*/

/**
	@id appendLlSeg

	@pre
    (head_1 == #head_1) * (last_next_1 == #last_next_1) * (head_2 == #head_2) * (last_next_2 == #last_next_2) *
    types(#list_2: $$list_type) *
    disjoint_ll_seg(#head_1, #last_next_1, #list_1, #last_next_2) *
    ll_seg(#head_2, #last_next_2, #list_2) *
    scope(append_ll_seg : #appendLlSeg) *
    fun_obj(appendLlSeg, #appendLlSeg, #appendLlSegProto)

	@post
    (#appended_list == (#list_1 @ #list_2)) *
    standardObject(ret) *
    dataField(ret, "head", #appended_head) *
    dataField(ret, "last_next", #last_next_2) *
    ll_seg(#appended_head, #last_next_2, #appended_list) *
    scope(append_ll_seg : #llSegToDllSeg) *
    fun_obj(appendLlSeg, #appendLlSeg, #appendLlSegProto)
*/
function append_ll_seg(head_1, last_next_1, head_2, last_next_2)
{
  /** @tactic unfold disjoint_ll_seg(#head_1, #last_next_1, #list_1, #last_next_2) */

  var return_obj = {
    head      : null,
    last_next : null
  };

  if (head_1 === last_next_1) { /* First list seg empty */

    /* Simply return the second list seg */
    return_obj.head      = head_2;
    return_obj.last_next = last_next_2;

    return return_obj;

  } else { /* First list seg non-empty */

    /* Recurse */
    var new_seg_obj = append_ll_seg(head_1.next, last_next_1, head_2, last_next_2);

    /* Update pointer to point to the appended segment */
    head_1.next = new_seg_obj.head;

    /* The result will be the updated head and the returned last_next */
    return_obj.head      = head_1;
    return_obj.last_next = new_seg_obj.last_next;

    /** @tactic fold ll_seg(#head_1, #last_2, (#list_1 @ #list_2)) */

    return return_obj;

  }

}
