/**

 @toprequires (emp)
 @topensures (scope(q: #q) * scope(r: #r) *
  Queue(#q, #pq_proto, #node_proto, #some_pri, 2) *
  standardObject(#r) * dataField(#r, "pri", 3) *
  dataField(#r, "val", #some_val) *
  (ret == $$undefined))

@pred Object (l, proto) :
	types (l : $$object_type) *
	((l, "@proto") -> proto) *
	((l, "@class") -> "Object") *
	((l, "@extensible") -> $$t);

@pred ErrorObjectWithMessage (l, m) :
  types (l : $$object_type) *
  ((l, "@proto") -> $lerr_proto) * ((l, "@class") -> "Error") *
  ((l, "@extensible") -> $$t) *
  ((l, "message") -> {{"d", m, $$t, $$f, $$t}});

@pred NodePrototype(np, insert_loc) :
	standardObject(np) *
	dataField(np, "insertToQueue", insert_loc) *
	fun_obj(insertToQueue, insert_loc, #insert_proto) *
	((np, "pri") -> None) *
	((np, "val") -> None) *
	((np, "next") -> None);

@pred Node(n, pri, val, next, node_proto) :
	Object(n, node_proto) *
	dataField(n, "pri",  pri) *
	dataField(n, "val",  val) *
	dataField(n, "next", next) *
	((n, "insertToQueue") -> None) *
	(0 <# pri) *
	types(pri : $$number_type, val : $$string_type, node_proto : $$object_type);

@pred NodeList(q, node_proto, max_pri, length) :
	(q == $$null) * (max_pri == 0) * (length == 0) * types(max_pri : $$number_type, length : $$number_type),

	Node(q, max_pri, #val, #next, node_proto) * (0 <# max_pri) *
	NodeList(#next, node_proto, #pri, #len_q) * (#pri <=# max_pri) *
  (length == #len_q + 1) *
	types(q : $$object_type, node_proto : $$object_type, #pri : $$number_type, max_pri : $$number_type, length : $$number_type, #len_q : $$number_type);

@pred QueuePrototype(pqp, enqueue_loc, enqueue_sc, dequeue_loc, dequeue_sc, n, node_proto, insert_loc) :
	standardObject(pqp) *
	dataField(pqp, "enqueue", enqueue_loc) *
  fun_obj(enqueue, enqueue_loc, #enqueue_proto, enqueue_sc) *
  dataField(pqp, "dequeue", dequeue_loc) *
	fun_obj(dequeue, dequeue_loc, #dequeue_proto, dequeue_sc) *
	((pqp, "_head") -> None) *
  fun_obj(Node, n, node_proto) *
  NodePrototype(node_proto, insert_loc);

  @pred Queue(pq, pq_proto, node_proto, max_pri, length) :
  	Object(pq, pq_proto) *
  	dataField(pq, "_head",  #head) *
    NodeList(#head, node_proto, max_pri, length) *
  	((pq, "enqueue") -> None) *
    ((pq, "dequeue") -> None) *
  	types(pq_proto : $$object_type, max_pri : $$number_type, length : $$number_type);
*/


var PriorityQueue;
 /** @id Module

    @pre (emp)

    @post ((ret == #pq) *
      fun_obj(PriorityQueue, #pq, #pq_proto, #pq_sc) *
      closure(Node: #n; PriorityQueue: #pq_sc, enqueue: #enqueue_sc, dequeue: #dequeue_sc) *
      QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc))

  */
PriorityQueue = (function () {

  /**
  	@id  Node

  	@pre (
  	   	(pri == #pri) * (val == #val) *
        types(#pri: $$number_type, #val: $$string_type) *
  	   	(0 <# #pri) *
  	   	((this, "pri") -> None) * ((this, "val") -> None) *
        ((this, "next") -> None) * ((this, "insertToQueue") -> None) *
  	   	Object(this, #node_proto) * NodePrototype(#node_proto, #insert_loc)
  	)

  	@post (
  	   		Node(this, #pri, #val, $$null, #node_proto) *
  	   		NodePrototype(#node_proto, #insert_loc) * (ret == $$empty) )
  */
   var Node = function (pri, val) {
      this.pri = pri; this.val = val; this.next = null;
   }

   /**
   	@id  insertToQueue

    @pre (
      (q == #q) *
      NodeList(#q, #node_proto, #pri_q, #length) *
      Node(this, #npri, #nval, $$null, #node_proto) *
      NodePrototype(#node_proto, #insert_loc) *
      (#pri_q <=# #npri) *
      types(#npri : $$number_type, #pri_q : $$number_type)
    )
    @post (
      NodeList(this, #node_proto, #npri, #length + 1) *
      (ret == this) *
      NodePrototype(#node_proto, #insert_loc)
    )

    @pre (
   		(q == #q) *
   		NodeList(#q, #node_proto, #pri_q, #length) *
   		Node(this, #npri, #nval, $$null, #node_proto) *
   		NodePrototype(#node_proto, #insert_loc) *
   		(#npri <# #pri_q) *
   		types(#npri : $$number_type, #pri_q : $$number_type)
   	)
   	@post (
   		NodeList(#q, #node_proto, #pri_q, #length + 1) * (ret == #q) *
   		NodePrototype(#node_proto, #insert_loc) * types(#q : $$object_type)
   	)


  */
   Node.prototype.insertToQueue = function (q) {
      /** @unfold NodeList(#q, #node_proto, #pri_q, #length) */
      if (q === null) {
         /** @fold NodeList(this, #node_proto, #npri, #length + 1) */
         return this
      }

      if (this.pri >= q.pri) {
         this.next = q;
         /** @fold NodeList(this, #node_proto, #npri, #length + 1) */
         return this
      }

      var tmp = this.insertToQueue (q.next);
      q.next = tmp;
      /** @fold NodeList(#q, #node_proto, #pri_q, #length + 1) */
      return q
   }

   /**
    @id  PriorityQueue

    @pre (
        ((this, "_head") -> None) *
        ((this, "enqueue") -> None) *
        ((this, "dequeue") -> None) *
        scope(Node: #n) *
        Object(this, #pq_proto) *
        QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc)
    )
    @post (
          Queue(this, #pq_proto, #node_proto, 0, 0) *
          QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc) *
          (ret == $$empty) * scope(Node: #n)
    )
   */
   var module = function () {
      /** @fold NodeList($$null, #node_proto, 0, 0) */
      this._head = null;
   };

   /**
     @id enqueue

      @pre (
        (pri == #npri) *
        (val == #nval) *
        (0 <# #npri) *
        scope(Node: #n) *
        Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
        QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc) *
        types(#npri : $$number_type, #nval: $$string_type) *
        (#pri_q <=# #npri)
      )
      @post (
        scope(Node: #n) *
        Queue(this, #pq_proto, #node_proto, #npri, #length + 1) *
        QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc) *
        (ret == $$empty)
      )

      @pre (
        (pri == #npri) *
        (val == #nval) *
        (0 <# #npri) *
        scope(Node: #n) *
        Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
        QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc) *
        types(#npri : $$number_type, #nval: $$string_type) *
        (#npri <# #pri_q)
      )
      @post (
        scope(Node: #n) *
        Queue(this, #pq_proto, #node_proto, #pri_q, #length + 1) *
        QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc) *
        (ret == $$empty)
      )

   */
   module.prototype.enqueue = function(pri, val) {
      var n = new Node(pri, val);
      this._head = n.insertToQueue(this._head);
   };

   /*
     @id dequeue
     @pre (
       scope(Node: #n) *
       Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
       (0 <# #length) *
       QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc)
     )
     @post (
       scope(Node: #n) *
       (#length == #new_length + 1) *
       Queue(this, #pq_proto, #node_proto, #new_pri_q, #new_length) *
       QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc) *
       standardObject(#r) * dataField(#r, "pri", #pri_q) *
       dataField(#r, "val", #some_val) * (ret == #r)
     )

     @pre (
       scope(Node: #n) *
       Queue(this, #pq_proto, #node_proto, 0, 0) *
       QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc)
     )
     @posterr (
       scope(Node: #n) *
       Queue(this, #pq_proto, #node_proto, 0, 0) *
       QueuePrototype(#pq_proto, #enqueue_loc, #enqueue_sc, #dequeue_loc, #dequeue_sc, #n, #node_proto, #insert_loc) *
       (err == #r) * ErrorObjectWithMessage(#r, "Queue is empty")
     )
   */
   module.prototype.dequeue = function () {
      /** @unfold NodeList(#head, #node_proto, #pri_q, #length) */
      if (this._head === null) {
        /** @fold NodeList(#head, #node_proto, #pri_q, #length) */
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
