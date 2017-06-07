/**


@pred Node(n, pri, val, next, np) :
	ObjectWithProto(n, np)     * types(np : $$object_type) *
	dataField(n, "pri",  pri)  * types(pri : $$number_type) * (0 <# pri) *
	dataField(n, "val",  val)  *
	dataField(n, "next", next) *
	((n, "insert") -> None);


@pred NodePrototype(np) :
	standardObject(np) *
	dataField(np, "insert", #insert_loc) *
	fun_obj(insert, #insert_loc, #insert_proto) *
	((np, "pri") -> None) *
	((np, "val") -> None) *
	((np, "next") -> None);


@pred NodeList(nl, np, max_pri, length) :
	(nl == $$null) * (max_pri == 0) * (length == 0) * types(max_pri : $$number_type, length : $$number_type),

	Node(nl, max_pri, #val, #next, np) * (0 <# max_pri) *
	NodeList(#next, np, #pri, #len_nl) * (#pri <=# max_pri) *
  	(length == #len_nl + 1) *
	types(nl : $$object_type, np : $$object_type, #pri : $$number_type, max_pri : $$number_type, length : $$number_type, #len_nl : $$number_type);


@pred Queue(pq, qp, np, max_pri, length) :
	ObjectWithProto(pq, qp) * types(qp : $$object_type) *
	dataField(pq, "_head",  #head) *
	NodeList(#head, np, max_pri, length) * types(max_pri : $$number_type, length : $$number_type) *
	((pq, "enqueue") -> None) *
	((pq, "dequeue") -> None);


@pred QueuePrototype(qp, np, c) :
	standardObject(qp) *
	dataField(qp, "enqueue", #enqueue_loc) *
	fun_obj(enqueue, #enqueue_loc, #enqueue_proto, #enqueue_sc) *
	dataField(qp, "dequeue", #dequeue_loc) *
	fun_obj(dequeue, #dequeue_loc, #dequeue_proto, #dequeue_sc) *
	((qp, "_head") -> None) *
	fun_obj(Node, #n, np, #node_sc) *
	NodePrototype(np) *
	closure(Node : #n, counter : c; Node : #node_sc, enqueue: #enqueue_sc, dequeue: #dequeue_sc);
*/

/** 
 	@id PQLib
*/
var PriorityQueue = (function () {

	var counter = 0;

	/**
	 	@id  Node
	
	 	@pre (
	 	   	(pri == #pri) * types(#pri: $$number_type) * (0 <# #pri) *
	 	   	(val == #val) *
	 	   	((this, "pri") -> None) * ((this, "val") -> None) * ((this, "next") -> None) * 
	 	   	((this, "insert") -> None) *
	 	   	ObjectWithProto(this, #np) * NodePrototype(#np) *
	 	   	scope(counter : #c) * types(#c : $$number_type)
	 	)
	
	 	@post (
			Node(this, #pri, #val, $$null, #np) * 
			NodePrototype(#np) * 
			scope(counter : #c + 1)
		)
	*/
	var Node = function (pri, val) {
		this.pri = pri; 
		this.val = val; 
		this.next = null;
		counter++
	}

	/**
		@id insert
		
		@pre (
			(nl == #nl) * 
			NodeList(#nl, #np, #pri_nl, #length) *
			Node(this, #npri, #nval, $$null, #np) *
			NodePrototype(#np) *
			(#pri_nl <# #npri) *
			types(#npri : $$number_type, #pri_nl : $$number_type)
		)
		
	    @post (
			NodeList(this, #np, #npri, #length + 1) *
			NodePrototype(#np) *
			(ret == this)
		)
	
	    @pre (
			(nl == #nl) *
			NodeList(#nl, #np, #pri_nl, #length) *
			Node(this, #npri, #nval, $$null, #np) *
			NodePrototype(#np) *
			(#npri <=# #pri_nl) *
			types(#npri : $$number_type, #pri_nl : $$number_type)
	   	)
	   	
	   	@post (
	   		types(#nl : $$object_type) *
			NodeList(#nl, #np, #pri_nl, #length + 1) *
			NodePrototype(#np) *
			(ret == #nl) 
		)
	*/
	Node.prototype.insert = function (nl) {
		/** @unfold NodeList(#nl, #np, #pri_nl, #length) */
		if (nl === null) {
		   /** @fold NodeList(this, #np, #npri, #length + 1) */
		   return this
		}
		
		if (this.pri > nl.pri) {
		   this.next = nl;
		   /** @fold NodeList(this, #np, #npri, #length + 1) */
		   return this
		}
		
		var tmp = this.insert (nl.next);
		nl.next = tmp;
		/** @fold NodeList(#nl, #np, #pri_nl, #length + 1) */
		return nl
	}

	var PQ = function () {
		/** @fold NodeList($$null, #np, 0, 0) */
		this._head = null;
	};

	/**
		@id enqueue
				
		@pre (
			(pri == #pri) * types(#pri : $$number_type) * (0 <# #pri) *
			(val == #val) *
			Queue(this, #pqp, #np, #pri_q, #length) *
			QueuePrototype(#pqp, #np, #c) *
			(#pri_q <# #npri)
		)
		
		@post (
			Queue(this, #pqp, #np, #npri, #length + 1) *
			QueuePrototype(#pqp, #n, #c + 1)
		)
	*/
	PQ.prototype.enqueue = function(pri, val) {
		var n = new Node(pri, val);
		this._head = n.insert(this._head);
		counter++
	};

	/**
		@id dequeue
	*/
   PQ.prototype.dequeue = function () {
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
