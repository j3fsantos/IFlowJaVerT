/**


@pred Object (l, proto) :
	types (l : $$object_type) *
	((l, "@proto") -> proto) *
	((l, "@class") -> "Object") *
	((l, "@extensible") -> $$t);

@pred NodePrototype(np, push_loc, insert_loc) :
	standardObject(np) *
	dataField(np, "push", push_loc) *
	fun_obj(push, push_loc, #push_proto) *
	dataField(np, "insert", insert_loc) *
	fun_obj(insert, insert_loc, #insert_proto) *
	((np, "pri") -> None) *
	((np, "val") -> None) *
	((np, "next") -> None);

@pred Node(n, pri, val, next, node_proto) :
	Object(n, node_proto) *
	dataField(n, "pri",  pri) *
    dataField(n, "val",  val) *
    dataField(n, "next", next) *
    ((n, "push") -> None) *
	((n, "insert") -> None) *
    types(pri : $$number_type, val : $$string_type, node_proto : $$object_type);

@pred Queue(q, node_proto, max_pri) :
	(q == $$null),

	Node(q, #pri, #val, #next, node_proto) *
	Queue(#next, node_proto, #pri) *
	(#pri <=# max_pri) *
	types(node_proto : $$object_type, #pri : $$number_type, max_pri : $$number_type);
*/

var counter = 0;

/**
	@id  Node

	@pre (
	   	scope(counter: #c) * types(#c : $$int_type) *
	   	(pri == #pri) * (val == #val) * types(#pri: $$number_type, #val: $$string_type) *
	   	((this, "pri") -> None) * ((this, "val") -> None) * ((this, "next") -> None) *
		((this, "push") -> None) * ((this, "insert") -> None) *
	   	Object(this, #node_proto) * NodePrototype(#node_proto, #push_loc, #insert_loc)
	)
	@post (
	   		scope(counter: #c + 1) *
	   		Node(this, #pri, #val, $$null, #node_proto) *
	   		NodePrototype(#node_proto, #push_loc, #insert_loc))
*/
var Node = function (pri, val) {
	this.pri = pri; this.val = val; this.next = null;
	counter++
}

/**
	@id  push

	@pre (
		(q == #q) *
		Node(this, #pri, #val, $$null, #node_proto) *
		Queue(#q, #node_proto, #pri_q) *
		NodePrototype(#node_proto, #push_loc, #insert_loc) *
		(#pri <# #pri_q) * types(#pri_q : $$number_type)
	)
	@post (
		Queue(#q, #node_proto, #pri_q) * (ret == #q) *
		NodePrototype(#node_proto, #push_loc, #insert_loc)
	)

	@pre (
		(q == #q) *
		Node(this, #pri, #val, $$null, #node_proto) *
		Queue(#q, #node_proto, #pri_q) *
		NodePrototype(#node_proto, #push_loc, #insert_loc) *
		(#pri_q <=# #pri) * types(#pri_q : $$number_type)
	)
	@post (
		Queue(this, #node_proto, #pri) * (ret == this) *
		NodePrototype(#node_proto, #push_loc, #insert_loc)
	)
*/
Node.prototype.push = function (q) {
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


/**
	@id  insert

	@pre (
		(this == #this) * (! (#this == $$null)) * (n == #n) *
		Queue(#this, #node_proto, #pri_q) *
	    Node(#n, #pri, #val, $$null, #node_proto) *
		NodePrototype(#node_proto, #push_loc, #insert_loc) *
		(#pri <=# #pri_q) *
		types(#pri : $$number_type, #pri_q : $$number_type, #this: $$object_type, #n : $$object_type)
	)
	@post (
		Queue(#this, #node_proto, #pri_q) * (ret == #this) *
		NodePrototype(#node_proto, #push_loc, #insert_loc)
	)

*/
Node.prototype.insert = function (n) {
	/** @unfold Queue(this, #node_proto, #pri_q) */
	if (n.pri > this.pri) {
		n.next = this;
		/** @fold Queue(#n, #node_proto, #pri) */
		return n
	} else {

		/** @invariant (
			scope(n : #n) *
			(this == #this) * (! (#this == $$null)) *
			Node(#this, #this_pri, #this_val, #this_next, #node_proto) *
			Queue(#this_next, #node_proto, #max_pri_next) *
			Node(#n, #pri, #val, $$null, #node_proto) *
			NodePrototype(#node_proto, #push_loc, #insert_loc) *
			(#this_pri <=# #pri_q) * 
			(#pri <=# #this_pri) * 
			scope(n: #n) * 
			types(#this : $$object_type, #this_pri : $$number_type, #this_val : $$string_type, 
			      #node_proto : $$object_type, #max_pri_next : $$number_type,
			      #n : $$object_type, #pri : $$number_type, #val : $$string_type, #push_loc : $$object_type, 
			      #pri_q : $$number_type, #insert_loc : $$object_type))

			@unfold Queue(#this_next, #node_proto, #max_pri_next) */
		var next = this.next;
		if (next == null) {
				this.next = n
		} else {
			   /* @fold Queue(#this_next, #node_proto, #max_pri_next) */
				var tmp = next.insert (n);
				this.next = tmp
		}
		/** @fold Queue(this, #node_proto, #pri_q) */
		return this
	}
}


/**
   @id  getCounter

   @pre  (scope(counter: #c) * types(#c : $$int_type))
   @post (scope(counter: #c) * (ret == #c))
*/
var getCounter = function () { return counter; };
