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
	(0 <# pri) *
	types(pri : $$number_type, val : $$string_type, node_proto : $$object_type);

@pred Queue(q, node_proto, max_pri, length) :
	(q == $$null) * (max_pri == 0) * (length == 0) * types(max_pri : $$number_type, length : $$number_type),

	Node(q, max_pri, #val, #next, node_proto) * (0 <# max_pri) *
	Queue(#next, node_proto, #pri, #len_q) * (#pri <=# max_pri) * (length == #len_q + 1) *
	types(q : $$object_type, node_proto : $$object_type, #pri : $$number_type, max_pri : $$number_type, length : $$number_type, #len_q : $$number_type);
*/

var counter = 0;

/**
	@id  Node

	@pre (
		scope(counter: #c) * types(#c : $$number_type) *
	   	(pri == #pri) * (val == #val) * types(#pri: $$number_type, #val: $$string_type) *
	   	(0 <# #pri) *
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
		Node(this, #npri, #nval, $$null, #node_proto) *
		Queue(#q, #node_proto, #pri_q, #length) *
		NodePrototype(#node_proto, #push_loc, #insert_loc) *
		(#npri <# #pri_q) * types(#npri : $$number_type, #pri_q : $$number_type, #length : $$number_type)
	)
	@post (
		Queue(#q, #node_proto, #pri_q, #length + 1) * (ret == #q) * types (#q : $$object_type) *
		NodePrototype(#node_proto, #push_loc, #insert_loc)
	)

	@pre (
		(q == #q) *
		Node(this, #npri, #val, $$null, #node_proto) *
		Queue(#q, #node_proto, #pri_q, #length) *
		NodePrototype(#node_proto, #push_loc, #insert_loc) *
		(#pri_q <=# #npri) * types(#npri : $$number_type, #pri_q : $$number_type, #length : $$number_type)
	)
	@post (
		Queue(this, #node_proto, #npri, #length + 1) * (ret == this) *
		NodePrototype(#node_proto, #push_loc, #insert_loc)
	)
*/
Node.prototype.push = function (q) {
	/** @unfold Queue(#q, #node_proto, #pri_q, #length) */
	if (q === null) {
		/** @fold Queue(this, #node_proto, #npri, 1) */
		return this
	}
	else
		if (this.pri >= q.pri) {
			this.next = q;
			/** @fold Queue(this, #node_proto, #npri, #length + 1) */
			return this
		}
		else
		{
			var tmp = this.push (q.next);
			q.next = tmp;
			/** @fold Queue(#q, #node_proto, #pri_q, #length + 1) */
			return q
		}
}


/**
	@id  insert

	@pre (
		(! (this == $$null)) *
		Queue(this, #node_proto, #pri_q, #length) *
		Node(n, #npri, #nval, $$null, #node_proto) *
		NodePrototype(#node_proto, #push_loc, #insert_loc) *
		(#npri <# #pri_q) *
		types(#npri : $$number_type, #pri_q : $$number_type, #n : $$object_type, #length : $$number_type)
	)
	@post (
		Queue(this, #node_proto, #pri_q, #length + 1) *
		(ret == this) *
		NodePrototype(#node_proto, #push_loc, #insert_loc)
	)

	@pre (
		(! (this == $$null)) * (n == #n) *
		Queue(this, #node_proto, #pri_q, #length) *
		Node(#n, #npri, #nval, $$null, #node_proto) *
		NodePrototype(#node_proto, #push_loc, #insert_loc) *
		(#pri_q <=# #npri) *
		types(#npri : $$number_type, #pri_q : $$number_type, #n : $$object_type)
	)
	@post (
		Queue(#n, #node_proto, #npri, #length + 1) * (ret == #n) *
		NodePrototype(#node_proto, #push_loc, #insert_loc)
	)

*/
Node.prototype.insert = function (n) {
	/** @unfold Queue(this, #node_proto, #pri_q, #length) */
	if (n.pri >= this.pri) {
		n.next = this;
		/** @fold Queue(#n, #node_proto, #npri, #length + 1) */
		return n
	} else {

		/**
			@unfold Queue(#this_next, #node_proto, #max_pri_next, #length - 1) */
		var next = this.next;
		if (next == null) {
				this.next = n
		} else {
			   /* @fold Queue(#this_next, #node_proto, #max_pri_next, #length - 1) */
				var tmp = next.insert (n);
				this.next = tmp
		}
		/** @fold Queue(this, #node_proto, #pri_q, #length + 1) */
		return this
	}
}


/**
   @id  getCounter

   @pre  (scope(counter: #c) * types(#c : $$number_type))
   @post (scope(counter: #c) * (ret == #c))
*/
var getCounter = function () { return counter; };


/**
   @id  incCounter

   @pre  (scope(counter: #c) * types(#c : $$number_type))
   @post (scope(counter: #c+1) * (ret == #c+1))
*/
var incCounter = function () { counter++; return counter; };