/**

@pred Object (l, proto) :
	types (l : $$object_type) *
	((l, "@proto") -> proto) *
	((l, "@class") -> "Object") *
	((l, "@extensible") -> $$t);

@pred NodePrototype(np, push_loc) :
	standardObject(np) *
	dataField(np, "push", push_loc) *
	fun_obj(push, push_loc, #push_proto) *
	((np, "pri") -> None) *
	((np, "elt") -> None) *
	((np, "next") -> None);

@pred Node(n, pri, elt, next, node_proto) :
	Object(n, node_proto) *
	dataField(n, "pri",  pri) *
    dataField(n, "elt",  elt) *
    dataField(n, "next", next) *
    ((n, "push") -> None) *
    types(pri : $$number_type, elt : $$string_type, node_proto : $$object_type);

@pred Queue(q, node_proto, max_pri) :
	(q == $$null),

	Node(q, #pri, #elt, #next, node_proto) *
	Queue(#next, node_proto, #pri) *
	(#pri <=# max_pri) *
	types(node_proto : $$object_type, #pri : $$number_type, max_pri : $$number_type);
*/

var counter = 0;

/**
	@id  Node
	@rec false

	@pre (
	   	scope(counter: #c) * types(#c : $$int_type) *
	   	(pri == #pri) * (elt == #elt) * types(#pri: $$number_type, #elt: $$string_type) *
	   	((this, "pri") -> None) * ((this, "elt") -> None) * ((this, "next") -> None) * ((this, "push") -> None) *
	   	Object(this, #node_proto) * NodePrototype(#node_proto, #push_loc)
	)
	@post (
	   		scope(counter: #c + 1) *
	   		Node(this, #pri, #elt, $$null, #node_proto) *
	   		NodePrototype(#node_proto, #push_loc))
*/
var Node = function (pri, elt) {
	this.pri = pri; this.elt = elt; this.next = null;
	counter++
}

/**
	@id  push
	@rec true

	@pre (
		(q == #q) *
		Node(this, #pri, #elt, $$null, #node_proto) *
		Queue(#q, #node_proto, #pri_q) *
		NodePrototype(#node_proto, #push_loc) *
		(#pri <# #pri_q) * types(#pri_q : $$number_type)
	)
	@post (
		Queue(#q, #node_proto, #pri_q) * (ret == #q) *
		NodePrototype(#node_proto, #push_loc)
	)

	@pre (
		(q == #q) *
		Node(this, #pri, #elt, $$null, #node_proto) *
		Queue(#q, #node_proto, #pri_q) *
		NodePrototype(#node_proto, #push_loc) *
		(#pri_q <=# #pri) * types(#pri_q : $$number_type)
	)
	@post (
		Queue(this, #node_proto, #pri) * (ret == this) *
		NodePrototype(#node_proto, #push_loc)
	)
*/
var push = function (q) {
	/** @unfold Queue(#q, #node_proto, #pri_q) */
	if (q === null) {
		/** @fold Queue(this, #node_proto, #pri) */
		return this
	}
	else
		if (this.pri >= q.pri) {
			this.next = q;
			/** @fold Queue(this, #node_proto, #pri) */
			return this
		}
		else
		{
			var tmp = this.push (q.next);
			q.next = tmp;
			/** @fold Queue(#q, #node_proto, #pri_q) */
			return q
		}
}


Node.prototype.push = push;


/**
   @id  getCounter
   @rec false

   @pre  (scope(counter: #c) * types(#c : $$int_type))
   @post (scope(counter: #c) * (ret == #c))
*/
var getCounter = function () { return counter; };
