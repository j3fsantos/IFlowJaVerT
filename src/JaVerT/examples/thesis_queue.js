/**

@pred Node(n, pri, val, next, np) :
	ObjectWithProto(n, np) *
	dataField(n, "pri",  pri) *
	dataField(n, "val",  val) *
	dataField(n, "next", next) *
	((n, "insertToQueue") -> None) *
	(0 <# pri) *
	types(pri : $$number_type, val : $$string_type, np : $$object_type);

  @pred NodePrototype(np) :
  	standardObject(np) *
  	dataField(np, "insertToQueue", #insert_loc) *
  	fun_obj(insertToQueue, #insert_loc, #insert_proto) *
  	((np, "pri") -> None) *
  	((np, "val") -> None) *
  	((np, "next") -> None);

@pred NodeList(nl, np, max_pri, length) :
	(nl == $$null) * (max_pri == 0) * (length == 0) * types(max_pri : $$number_type, length : $$number_type),

	Node(nl, max_pri, #val, #next, np) * (0 <# max_pri) *
	NodeList(#next, np, #pri, #len_nl) * (#pri <=# max_pri) *
  (length == #len_nl + 1) *
	types(nl : $$object_type, np : $$object_type, #pri : $$number_type, max_pri : $$number_type, length : $$number_type, #len_nl : $$number_type);

  @pred Queue(pq, pqp, np, max_pri, length) :
  	ObjectWithProto(pq, pqp) *
  	dataField(pq, "_head",  #head) *
    NodeList(#head, np, max_pri, length) *
  	((pq, "enqueue") -> None) *
    ((pq, "dequeue") -> None) *
  	types(pqp : $$object_type, max_pri : $$number_type, length : $$number_type);


@pred QueuePrototype(pqp, np, enq_sc) :
  standardObject(pqp) *
  dataField(pqp, "enqueue", #enqueue_loc) *
  fun_obj(enqueue, #enqueue_loc, #enqueue_proto, enq_sc) *
  dataField(pqp, "dequeue", #dequeue_loc) *
  fun_obj(dequeue, #dequeue_loc, #dequeue_proto, #dequeue_sc) *
  ((pqp, "_head") -> None) *
  fun_obj(Node, #n, np, #node_sc) *
  closure(Node : #n; enqueue: enq_sc) *
  NodePrototype(np)
    ;

@pred PriorityQueueModule(pq) :
  QueuePrototype(#pqp, #np, #sc) *
  fun_obj(PriorityQueue, pq, #pqp, #pq_sc) *
  o_chains(PriorityQueue: #pq_sc, enqueue: #sc);

*/

/**
@toprequires (emp)
@topensures (scope(q: #q) * scope(r: #r) *
 Queue(#q, #pqp, #np, #some_pri, 2) *
 standardObject(#r) * dataField(#r, "pri", 3) *
 dataField(#r, "val", #some_val) *
 (ret == $$undefined))
*/


var PriorityQueue;
 /** @id Module

    @pre (emp)

    @post ((ret == #pq) * PriorityQueueModule(#pq))

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
  	   	ObjectWithProto(this, #np) * NodePrototype(#np)
  	)

  	@post (
  	   		Node(this, #pri, #val, $$null, #np) *
  	   		NodePrototype(#np)
  	)
  */
   var Node = function (pri, val) {
      this.pri = pri; this.val = val; this.next = null;
   }

   /**
   	@id  insertToQueue

    @pre (
      (q == #q) *
      NodeList(#q, #np, #pri_q, #length) *
      Node(this, #npri, #nval, $$null, #np) *
      NodePrototype(#np) *
      (#pri_q <=# #npri) *
      types(#npri : $$number_type, #pri_q : $$number_type)
    )
    @post (
      NodeList(this, #np, #npri, #length + 1) *
      (ret == this) *
      NodePrototype(#np)
    )

    @pre (
   		(q == #q) *
   		NodeList(#q, #np, #pri_q, #length) *
   		Node(this, #npri, #nval, $$null, #np) *
   		NodePrototype(#np) *
   		(#npri <# #pri_q) *
   		types(#npri : $$number_type, #pri_q : $$number_type)
   	)
   	@post (
   		NodeList(#q, #np, #pri_q, #length + 1) * (ret == #q) *
   		NodePrototype(#np) * types(#q : $$object_type)
   	)


  */
   Node.prototype.insertToQueue = function (q) {
      /** @tactic unfold NodeList(#q, #node_proto, #pri_q, #length) */
      if (q === null) {
         /** @tactic fold NodeList(this, #node_proto, #npri, #length + 1) */
         return this
      }

      if (this.pri >= q.pri) {
         this.next = q;
         /** @tactic fold NodeList(this, #node_proto, #npri, #length + 1) */
         return this
      }

      var tmp = this.insertToQueue (q.next);
      q.next = tmp;
      /** @tactic fold NodeList(#q, #node_proto, #pri_q, #length + 1) */
      return q
   }

   /**
    @id  PriorityQueue

    @pre (
        ((this, "_head") -> None) *
        ((this, "enqueue") -> None) *
        ((this, "dequeue") -> None) *
        ObjectWithProto(this, #pqp) *
        QueuePrototype(#pqp, #np, #sc)
    )
    @post (
          Queue(this, #pqp, #np, 0, 0) *
          QueuePrototype(#pqp, #np, #sc)
    )
   */
   var module = function () {
      /** @tactic fold NodeList($$null, #np, 0, 0) */
      this._head = null;
   };

   /**
     @id enqueue

      @pre (
        (pri == #npri) *
        (val == #nval) *
        (0 <# #npri) *
        o_sc(enqueue: #sc) *
        Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
        QueuePrototype(#pq_proto, #node_proto, #sc) *
        types(#npri : $$number_type, #nval: $$string_type) *
        (#pri_q <=# #npri)
      )
      @post (
        Queue(this, #pq_proto, #node_proto, #npri, #length + 1) *
        QueuePrototype(#pq_proto, #node_proto, #sc)
      )

      @pre (
        (pri == #npri) *
        (val == #nval) *
        (0 <# #npri) *
        o_sc(enqueue: #sc) *
        Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
        QueuePrototype(#pq_proto, #node_proto, #sc) *
        types(#npri : $$number_type, #nval: $$string_type) *
        (#npri <# #pri_q)
      )
      @post (
        Queue(this, #pq_proto, #node_proto, #pri_q, #length + 1) *
        QueuePrototype(#pq_proto, #node_proto, #sc)
      )

   */
   module.prototype.enqueue = function(pri, val) {
      var n = new Node(pri, val);
      this._head = n.insertToQueue(this._head);
   };

   /*
     @id dequeue
     @pre (
       Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
       (0 <# #length) *
       QueuePrototype(#pq_proto, #node_proto, #sc)
     )
     @post (
       (#length == #new_length + 1) *
       Queue(this, #pq_proto, #node_proto, #new_pri_q, #new_length) *
       QueuePrototype(#pq_proto, #node_proto, #sc) *
       standardObject(#r) * dataField(#r, "pri", #pri_q) *
       dataField(#r, "val", #some_val) * (ret == #r)
     )

     @pre (
       Queue(this, #pq_proto, #node_proto, 0, 0) *
       QueuePrototype(#pq_proto, #node_proto, #sc)
     )
     @posterr (
       Queue(this, #pq_proto, #node_proto, 0, 0) *
       QueuePrototype(#pq_proto, #node_proto, #sc) *
       (err == #r) * ErrorObjectWithMessage(#r, "Queue is empty")
     )
   */
   module.prototype.dequeue = function () {
      /** @tactic unfold NodeList(#head, #node_proto, #pri_q, #length) */
      if (this._head === null) {
        /** @tactic fold NodeList(#head, #node_proto, #pri_q, #length) */
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
