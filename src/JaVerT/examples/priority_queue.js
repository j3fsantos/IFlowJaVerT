/**
	@pred Node(n, pri, val, next, np) :
		JSObjWithProto(n, np)      * 
		DataProp(n, "pri",  pri)   * (0 <# pri) *
		DataProp(n, "val",  val)   *
		DataProp(n, "next", next)  *
		((n, "insert") -> none);
	
	
	@pred NodePrototype(np) :
		JSObject(np) *
		DataProp(np, "insert", #insert_loc) *
		JSFunctionObject(#insert_loc, "insert", _, _, _) *
		((np, "pri") -> none) * 
		((np, "val") -> none) * 
		((np, "next") -> none);
	
	@pred NodeList(nl, np, max_pri, length) :
		(nl == null) * (max_pri == 0) * (length == 0),
	
		Node(nl, max_pri, #val, #next, np) * (0 <# max_pri) *
		NodeList(#next, np, #pri, #len_nl) * (#pri <=# max_pri) *
	  	(length == #len_nl + 1);
	
	
	@pred Queue(pq, qp, np, max_pri : Num, length : Num) :
		JSObjWithProto(pq, qp) * 
		DataProp(pq, "_head",  #head) *
		NodeList(#head, np, max_pri, length) *
		((pq, "enqueue") -> none) * 
		((pq, "dequeue") -> none);
	
	
	@pred QueuePrototype(qp, np, c : Num, enq_sc):
		JSObject(qp) *
		DataProp(qp, "enqueue", #enqueue_loc) * JSFunctionObject(#enqueue_loc, "enqueue", enq_sc, _, _) *
		DataProp(qp, "dequeue", #dequeue_loc) * JSFunctionObject(#dequeue_loc, "dequeue", #dequeue_sc, _, _) *
		((qp, "_head") -> none) *
		JSFunctionObject(#n, "Node", #node_sc, _, np) * NodePrototype(np) * 
		closure(Node : #n, counter : c; Node : #node_sc, enqueue: enq_sc, dequeue: #dequeue_sc);
	
	@pred PriorityQueueModule(pq) :
	  QueuePrototype(#pqp, #np, 0, #sc) *
	  JSFunctionObject(pq, "PriorityQueue", #pq_sc, _, #pqp) *
	  o_chains(PriorityQueue: #pq_sc, enqueue: #sc);
*/

/**
	@toprequires (initialHeapPre())
	@topensures (
		scope(q : #q) * scope(r : #r) *
		Queue(#q, #pqp, #np, #pri_q, 2) *
		JSObject(#r) * DataProp(#r, "pri", #3) * DataProp(#r, "val", _) * (ret == #r)
	)
*/

/** 
 	@id PQLib
    @pre  (initialHeapPostWeak())
    @post (initialHeapPostWeak() * PriorityQueueModule (ret))
*/
var PriorityQueue = (function () {

	var counter = 0;

	/**
	 	@id  Node
	
	 	@pre (
	 		initialHeapPostWeak() * 
	 	   	(pri == #pri) * (0 <# #pri) *
	 	   	(val == #val) *
	 	   	((this, "pri") -> none) * ((this, "val") -> none) * ((this, "next") -> none) * 
	 	   	((this, "insert") -> none) *
	 	   	JSObjWithProto(this, #np) * NodePrototype(#np) *
	 	   	scope(counter : #c) * types(#c : Num) 
	 	)
	 	@post (
	 		initialHeapPostWeak() * 
			Node(this, #pri, #val, null, #np) * 
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
			Node(this, #npri, #nval, null, #np) *
			NodePrototype(#np) *
			(#pri_nl <# #npri)
		)
	    @post (
			NodeList(this, #np, #npri, #length + 1) *
			NodePrototype(#np) *
			(ret == this)
		)
	
	    @pre (
			(nl == #nl) *
			NodeList(#nl, #np, #pri_nl, #length) *
			Node(this, #npri, #nval, null, #np) *
			NodePrototype(#np) *
			(#npri <=# #pri_nl)
	   	)
	   	@post (
	   		types(#nl : Obj) *
			NodeList(#nl, #np, #pri_nl, #length + 1) *
			NodePrototype(#np) *
			(ret == #nl) 
		)
	*/
	Node.prototype.insert = function (nl) {
		/** @tactic unfold NodeList(#nl, #np, #pri_nl, #length) */
		if (nl === null) {
		   /** @tactic fold NodeList(this, #np, #npri, #length + 1) */
		   return this
		}
		
		if (this.pri > nl.pri) {
		   this.next = nl;
		   /** @tactic fold NodeList(this, #np, #npri, #length + 1) */
		   return this
		}
		
		var tmp = this.insert (nl.next);
		nl.next = tmp;
		/** @tactic fold NodeList(#nl, #np, #pri_nl, #length + 1) */
		return nl
	}

	/**
	    @id  PriorityQueue
	
		@pre (
			initialHeapPostWeak() * 
	        ((this, "_head") -> none) *
	        ((this, "enqueue") -> none) *
	        ((this, "dequeue") -> none) *
	        JSObjWithProto(this, #pqp) *
	        o_chains(enqueue: #sc, PQLib: $$scope) *
	        QueuePrototype(#pqp, #np, #c, #sc)
	    )
	    @post (
	    	initialHeapPostWeak() * 
	    	Queue(this, #pqp, #np, 0, 0) *
	    	QueuePrototype(#pqp, #np, #c, #sc)
	    )
	*/
	var PQ = function () {
		/** @tactic fold NodeList(null, #np, 0, 0) */
		this._head = null;
	};

	/**
		@id enqueue
				
		@pre (
			initialHeapPostWeak() * 
			(pri == #pri) * (0 <# #pri) *
			(val == #val) * 
			Queue(this, #pqp, #np, #pri_q, #length) *
			QueuePrototype(#pqp, #np, #c, #sc) *
			o_chains(enqueue: #sc, PQLib: $$scope) *
			(#pri <=# #pri_q)
		)
		@post (
			initialHeapPostWeak() * 
			Queue(this, #pqp, #np, #pri_q, #length + 1) *
			QueuePrototype(#pqp, #np, #c + 1, #sc)
		)
		
		@pre (
			initialHeapPostWeak() * 
			(pri == #pri) * (0 <# #pri) *
			(val == #val) * 
			Queue(this, #pqp, #np, #pri_q, #length) *
			QueuePrototype(#pqp, #np, #c, #sc) *
			o_chains(enqueue: #sc, PQLib: $$scope) *
			(#pri_q <# #pri)
		)
		@post (
			initialHeapPostWeak() * 
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
       o_chains(enqueue: #sc, dequeue: $$scope) *
       (0 <# #length)
     )
     @post (
       Queue(this, #pqp, #np, #new_pri_q, #length - 1) *
       QueuePrototype(#pqp, #np, #c - 1, #sc) *
       (ret == #r) * JSObject(#r) * 
       DataProp(#r, "pri", #pri_q) * DataProp(#r, "val", #some_val)
     )
     @pre (
       initialHeapPostWeak() * 
       Queue(this, #pqp, #np, 0, 0) *
       QueuePrototype(#pqp, #np, #c, #sc) *
       o_chains(enqueue: #sc, dequeue: $$scope)
     )
     @posterr (
       initialHeapPostWeak() * 
       Queue(this, #pqp, #np, 0, 0) *
       QueuePrototype(#pqp, #np, #c, #sc) *
       (err == #e) * ErrorObjectWithMessage(#e, "Queue is empty")
     )
   */
   PQ.prototype.dequeue = function () {
      /** @tactic unfold NodeList(#head, #np, #pri_q, #length) */
      if (this._head === null) {
        /** @tactic fold NodeList(#head, #np, #pri_q, #length) */
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