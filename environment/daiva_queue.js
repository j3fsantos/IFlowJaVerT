/*
	@pred Node(n, pri, val, next, node_proto) :
		ObjectWithProto(n, node_proto) *
		dataField(n, "pri",  pri) *
		dataField(n, "val",  val) *
		dataField(n, "next", next) *
		((n, "insertToQueue") -> None) *
		(0 <# pri) *
		types(pri : $$number_type, node_proto : $$object_type);

	@pred NodePrototype(np, insertToQueue_loc) :
		standardObject(np) *
		dataField(np, "insertToQueue", insertToQueue_loc) *
		fun_obj(insertToQueue, insertToQueue_loc, #insertToQueue_proto) *
		((np,  "pri") -> None) *
		((np,  "val") -> None) *
		((np, "next") -> None);
		
	@pred Queue(q, max_pri, node_proto) :
		(q == $$null) * (max_pri == 0) * types(max_pri : $$number_type),
		
		Node(q, max_pri, #val, #next, node_proto) * 
		Queue(#next, #pri, node_proto) * (#pri <=# max_pri) *
		types(q : $$object_type, node_proto : $$object_type, #pri : $$number_type, max_pri : $$number_type);
*/

/* @id Module */
var PriorityQueue = (function () {

	/**
		@id  Node

		@pre (
			(pri == #pri) * (val == #val) * types(#pri: $$number_type) *
			(0 <# #pri) *
			((this, "pri") -> None) * ((this, "val") -> None) * ((this, "next") -> None) *
			((this, "insertToQueue") -> None) *
			ObjectWithProto(this, #node_proto) * 
			NodePrototype(#node_proto, #insertToQueue_loc)
		)

		@post (
			Node(this, #pri, #val, $$null, #node_proto) *
			NodePrototype(#node_proto, #insertToQueue_loc))
	*/
	var Node = function (pri, val) {
	  this.pri = pri; this.val = val; this.next = null;
	}

	/**
		@id  insertToQueue

		@pre (
			(q == #q) *
			Node(this, #npri, #val, $$null, #node_proto) *
			Queue(#q, #pri_q, #node_proto) *
			NodePrototype(#node_proto, #insertToQueue_loc) *
			(#pri_q <=# #npri) * types(#npri : $$number_type, #pri_q : $$number_type)
		)
		
		@post (
			Queue(this, #npri, #node_proto) * (ret == this) *
			NodePrototype(#node_proto, #insertToQueue_loc)
		)
		
		@pre (
			(q == #q) *
			Node(this, #npri, #nval, $$null, #node_proto) *
			Queue(#q, #pri_q, #node_proto) *
			NodePrototype(#node_proto, #insertToQueue_loc) *
			(#npri <# #pri_q) * types(#npri : $$number_type, #pri_q : $$number_type)
		)
		@post (
			Queue(#q, #pri_q, #node_proto) * (ret == #q) * types (#q : $$object_type) *
			NodePrototype(#node_proto, #insertToQueue_loc)
		)
	*/
	Node.prototype.insertToQueue = function (q) {
		/** @unfold Queue(#q, #pri_q, #node_proto) */
		if (q === null) {
			/** @fold Queue(this, #npri, #node_proto) */
			return this
		}

		if (this.pri >= q.pri) {
			this.next = q;
			/** @fold Queue(this, #npri, #node_proto) */
			return this
		}

		var tmp = this.insertToQueue (q.next);
		q.next = tmp;
		/** @fold Queue(#q, #pri_q, #node_proto) */
		return q
	}
	
   /* @id PriorityQueue */
   var module = function () {
      this._head = null;
   };

   /* @id enqueue */
   module.prototype.enqueue = function(pri, val) {	    	  
      var n = new Node(pri, val);
      this._head = n.insertToQueue(this._head); 		
   };

   /* @id dequeue */	    
   module.prototype.dequeue = function () {
      if (this._head === null) {
         throw new Error("Queue is empty");
      } 
        			
      var first = this._head;
      this._head = this._head.next;
      return {pri: first.pri, val: first.val};
   };
   
   return module;
})();

var q = new PriorityQueue();
q.enqueue(1, "last");
q.enqueue(3, "bar");
q.enqueue(2, "foo");
var r = q.dequeue();