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
	
	
	@pred QueuePrototype(qp, np, c, enq_sc):
		standardObject(qp) *
		dataField(qp, "enqueue", #enqueue_loc) *
		fun_obj(enqueue, #enqueue_loc, #enqueue_proto, enq_sc) *
		dataField(qp, "dequeue", #dequeue_loc) *
		fun_obj(dequeue, #dequeue_loc, #dequeue_proto, #dequeue_sc) *
		((qp, "_head") -> None) *
		fun_obj(Node, #n, np, #node_sc) *
		NodePrototype(np) * 
		closure(Node : #n, counter : c; Node : #node_sc, enqueue: enq_sc, dequeue: #dequeue_sc) * 
		types(c : $$number_type);
	
	@pred PriorityQueueModule(pq) :
	  QueuePrototype(#pqp, #np, 0, #sc) *
	  fun_obj(PriorityQueue, pq, #pqp, #pq_sc) *
	  o_chains(PriorityQueue: #pq_sc, enqueue: #sc);
*/

/**
	@toprequires 
		emp
	
	@topensures
		scope(q : #q) * scope(r : #r) *
		Queue(#q, #pqp, #np, #pri_q, 2) *
		standardObject(#r) * dataField(#r, "pri", #3) *
		dataField(#r, "val", #some_val) *
		(ret == #r)
*/

/** 
 	@id PQLib
    @pre (emp)
    @post ((ret == #pq) * PriorityQueueModule(#pq))
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

	/**
	    @id  PriorityQueue
	
		@pre (
	        ((this, "_head") -> None) *
	        ((this, "enqueue") -> None) *
	        ((this, "dequeue") -> None) *
	        ObjectWithProto(this, #pqp) *
	        overlaps_with_current_scope(enqueue: #sc) *
	        QueuePrototype(#pqp, #np, #c, #sc)
	    )
	    @post (
	    	Queue(this, #pqp, #np, 0, 0) *
	    	QueuePrototype(#pqp, #np, #c, #sc)
	    )
	*/
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
			QueuePrototype(#pqp, #np, #c, #sc) *
			overlaps_with_current_scope(enqueue: #sc) *
			(#pri <=# #pri_q)
		)
		@post (
			Queue(this, #pqp, #np, #pri_q, #length + 1) *
			QueuePrototype(#pqp, #np, #c + 1, #sc)
		)
		
		@pre (
			(pri == #pri) * types(#pri : $$number_type) * (0 <# #pri) *
			(val == #val) *
			Queue(this, #pqp, #np, #pri_q, #length) *
			QueuePrototype(#pqp, #np, #c, #sc) *
			overlaps_with_current_scope(enqueue: #sc) *
			(#pri_q <# #pri)
		)
		@post (
			Queue(this, #pqp, #np, #pri, #length + 1) *
			QueuePrototype(#pqp, #np, #c + 1, #sc)
		)
	*/
	PQ.prototype.enqueue = function(pri, val) {
		var n = new Node(pri, val);
		this._head = n.insert(this._head);
	};

   /*
     @id dequeue
     
     @pre (
       Queue(this, #pqp, #np, #pri_q, #length) * 
       QueuePrototype(#pqp, #np, #c, #sc) *
       overlaps_with_current_scope(enqueue: #sc) *
       (0 <# #length)
     )
     @post (
       Queue(this, #pqp, #np, #new_pri_q, #length - 1) *
       QueuePrototype(#pqp, #np, #c - 1, #sc) *
       (ret == #r) * standardObject(#r) * 
       dataField(#r, "pri", #pri_q) * dataField(#r, "val", #some_val)
     )
     @pre (
       Queue(this, #pqp, #np, 0, 0) *
       QueuePrototype(#pqp, #np, #c, #sc) *
       overlaps_with_current_scope(enqueue: #sc)
     )
     @posterr (
       Queue(this, #pqp, #np, 0, 0) *
       QueuePrototype(#pqp, #np, #c, #sc) *
       (err == #e) * ErrorObjectWithMessage(#e, "Queue is empty")
     )
   */
   PQ.prototype.dequeue = function () {
      /** @unfold NodeList(#head, #np, #pri_q, #length) */
      if (this._head === null) {
        /** @fold NodeList(#head, #np, #pri_q, #length) */
        throw new Error("Queue is empty");
      }

	  counter--;
      var first = this._head;
      this._head = this._head.next;
      return {pri: first.pri, val: first.val};
   };

   return PQ;
})();

var q, r;

q = new PriorityQueue();
q.enqueue(2, "last");
q.enqueue(4, "bar");
q.enqueue(3, "foo");
r = q.dequeue();
q.enqueue(1, "baz");
r = q.dequeue();