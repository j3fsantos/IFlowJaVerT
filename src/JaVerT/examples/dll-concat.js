/**
@pred dll_node(node, val, next, prev):
  standardObject(node) *
  dataField(node, "value", val) *
  dataField(node, "next", next) *
  dataField(node, "prev", prev) *
  empty_fields(node : -{"value", "next", "prev"}-);

(* Unfolds from the left *)
@pred dll_seg(head, head_prev, last, last_next, list):
  types(list: $$list_type) *
  (list == {{ }}) *
  (head_prev == last) *
  (head == last_next),

  (! (head == last_next)) *
  types(list: $$list_type) *
  (list == (#item :: #items)) *
  (dll_node(head, #item, #next, head_prev)) *
  (dll_seg(#next, head, last, last_next, #items));

(* Unfolds from the right *)
@pred dll_seg_2(head, head_prev, last, last_next, list):
  types(list: $$list_type) *
  (list == {{ }}) *
  (head_prev == last) *
  (head == last_next),

  (! (head == last_next)) *
  (list == (#items @ {{ #item }})) *
  types(list: $$list_type, #items: $$list_type, head: $$object_type, last: $$object_type) *
  (dll_node(last, #item, last_next, #last_prev)) *
  (dll_seg_2(head, head_prev, #last_prev, last, #items));

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
@onlyspec switch_end_to_right(head, head_prev, last, last_next, list)
  pre:  [[ dll_seg(head, head_prev, last, last_next, list) ]]
  post: [[ dll_seg_2(head, head_prev, last, last_next, list) ]]
  outcome: normal

@onlyspec switch_end_to_left(head, head_prev, last, last_next, list)
  pre:  [[ dll_seg_2(head, head_prev, last, last_next, list) ]]
  post: [[ dll_seg(head, head_prev, last, last_next, list) ]]
  outcome: normal

@onlyspec concat_dll_segs(head_1, head_prev_1, last_1, last_next_1, list_1, head_2, head_prev_2, last_2, last_next_2, list_2)
  pre:  [[ (head_1 == #head_1) * (head_prev_1 == #head_prev_1) * (last_1 == #last_1) * (last_next_1 == #last_next_1) * (list_1 == #list_1) *
           (head_2 == #head_2) * (head_prev_2 == #head_prev_2) * (last_2 == #last_2) * (last_next_2 == #last_next_2) * (list_2 == #list_2) *
           dll_seg(#head_1, #head_prev_1, #last_1, #last_next_1, #list_1) *
           dll_seg(#head_2, #head_prev_2, #last_2, #last_next_2, #list_2) *
           (#last_next_1 == #head_2) *
           (#head_prev_2 == #last_1) ]]
  post: [[ (#concat_list == (#list_1 @ #list_2)) *
           dll_seg(#head_1, #head_prev_1, #last_2, #last_next_2, #concat_list) ]]
  outcome: normal
*/

/**
	@id appendDllObj

	@pre
    (dll_obj_1 == #dll_obj_1) * (dll_obj_2 == #dll_obj_2) *
    (! (#head_1 == #head_2)) *
    dll_obj(#dll_obj_1, #head_1, #head_prev_1, #last_1, #last_next_1, #list_1) *
    dll_obj(#dll_obj_2, #head_2, #head_prev_2, #last_2, #last_next_2, #list_2) *
    scope(append_dll_obj : #appendDllObj) *
    fun_obj(appendDllObj, #appendDllObj, #appendDllObjProto)

	@post
    (#appended_list == (#list_1 @ #list_2)) *
    dll_obj(ret, #appended_head, #appended_head_prev, #appended_last, #appended_last_next, #appended_list) *
    scope(append_dll_obj : #appendDllObj) *
    fun_obj(appendDllObj, #appendDllObj, #appendDllObjProto)
*/
function append_dll_obj(dll_obj_1, dll_obj_2)
{

  /** Unfold first seg from right */
  /** @tactic callspec switch_end_to_right(#ignore, #head_1, #head_prev_1, #last_1, #last_next_1, #list_1) */
  /** @tactic unfold dll_seg_2(#head_1, #head_prev_1, #last_1, #last_next_1, #list_1) */

  if (dll_obj_1.head === dll_obj_1.last_next) { /** First list empty */

    /** Simply return the second dll object */
    return dll_obj_2;

  } else { /** First list non-empty */

    /** @tactic unfold dll_seg(#head_2, #head_prev_2, #last_2, #last_next_2, #list_2) */

    if (dll_obj_2.head === dll_obj_2.last_next) { /** Second list empty */

      /** Simply return the first dll object */

      /** Collapse and switch the first seg back to the left ready to return */
      /** @tactic fold dll_seg_2(#head_1, #head_prev_1, #last_1, #last_next_1, #list_1) */
      /** @tactic callspec switch_end_to_left(#ignore, #head_1, #head_prev_1, #last_1, #last_next_1, #list_1) */

      return dll_obj_1;

    } else { /** Both lists non-empty */

      /** Set forwards pointer of first dll */
      var last_1  = dll_obj_1.last;
      last_1.next = dll_obj_2.head;

      /** Set backwards pointer of second dll */
      var head_2  = dll_obj_2.head;
      head_2.prev = last_1;

      /** Collapse both the list preds and flip the first back to the left
         then axiomatically concatenate the segs */
      /** @tactic fold dll_seg(#head_2, #last_1, #last_2, #last_next_2, #list_2) */
      /** @tactic fold dll_seg_2(#head_1, #head_prev_1, #last_1, #head_2, #list_1) */
      /** @tactic callspec switch_end_to_left(#ignore, #head_1, #head_prev_1, #last_1, #head_2, #list_1) */
      /** @tactic callspec concat_dll_segs(#ignore, #head_1, #head_prev_1, #last_1, #head_2, #list_1, #head_2, #last_1, #last_2, #last_next_2, #list_2) */

      /** Re-use the first dll obj */
      dll_obj_1.last      = dll_obj_2.last;
      dll_obj_1.last_next = dll_obj_2.last_next;
      return dll_obj_1;

    }

  }

}
