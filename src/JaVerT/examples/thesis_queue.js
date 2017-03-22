/**

 @toprequires (emp)
 @topensures (scope(q: #q) * scope(r: #r) *
  Queue(#q, #pq_proto, #node_proto, #some_pri, 2) *
  standardObject(#r) * dataField(#r, "pri", 3) *
  dataField(#r, "val", #some_val) *
  (ret == $$undefined))

@pred NodePrototype(np) :
	standardObject(np) *
	dataField(np, "insertToQueue", #insert_loc) *
	fun_obj(insertToQueue, #insert_loc, #insert_proto) *
	((np, "pri") -> None) *
	((np, "val") -> None) *
	((np, "next") -> None);

@pred Node(n, pri, val, next, node_proto) :
	ObjectWithProto(n, node_proto) *
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

@pred QueuePrototype(pqp, n, np) :
	standardObject(pqp) *
	dataField(pqp, "enqueue", #enqueue_loc) *
  	fun_obj(enqueue, #enqueue_loc, #enqueue_proto, #enqueue_sc) *
 	dataField(pqp, "dequeue", #dequeue_loc) *
	fun_obj(dequeue, #dequeue_loc, #dequeue_proto, #dequeue_sc) *
	((pqp, "_head") -> None) *
  	fun_obj(Node, n, np) *
  	NodePrototype(np) *
  	closure(Node: n; enqueue: #enqueue_sc)
  	;

  @pred Queue(pq, pqp, np, max_pri, length) :
  	ObjectWithProto(pq, pqp) *
  	dataField(pq, "_head",  #head) *
    NodeList(#head, np, max_pri, length) *
  	((pq, "enqueue") -> None) *
    ((pq, "dequeue") -> None) *
  	types(pqp : $$object_type, max_pri : $$number_type, length : $$number_type);
*/


var PriorityQueue;
 /** @id Module

    @pre (emp)

    @post ((ret == #pq) *
      fun_obj(PriorityQueue, #pq, #pq_proto, #pq_sc) *
      QueuePrototype(#pq_proto, #n, #node_proto))

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
  	   	ObjectWithProto(this, #node_proto) * NodePrototype(#node_proto)
  	)

  	@post (
  	   		Node(this, #pri, #val, $$null, #node_proto) *
  	   		NodePrototype(#node_proto) * (ret == $$empty) )
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
      NodePrototype(#node_proto) *
      (#pri_q <=# #npri) *
      types(#npri : $$number_type, #pri_q : $$number_type)
    )
    @post (
      NodeList(this, #node_proto, #npri, #length + 1) *
      (ret == this) *
      NodePrototype(#node_proto)
    )

    @pre (
   		(q == #q) *
   		NodeList(#q, #node_proto, #pri_q, #length) *
   		Node(this, #npri, #nval, $$null, #node_proto) *
   		NodePrototype(#node_proto) *
   		(#npri <# #pri_q) *
   		types(#npri : $$number_type, #pri_q : $$number_type)
   	)
   	@post (
   		NodeList(#q, #node_proto, #pri_q, #length + 1) * (ret == #q) *
   		NodePrototype(#node_proto) * types(#q : $$object_type)
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
        ObjectWithProto(this, #pq_proto) *
        QueuePrototype(#pq_proto, #n, #node_proto)
    )
    @post (
          Queue(this, #pq_proto, #node_proto, 0, 0) *
          QueuePrototype(#pq_proto, #n, #node_proto) *
          (ret == $$empty)
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
        QueuePrototype(#pq_proto, #n, #node_proto) *
        types(#npri : $$number_type, #nval: $$string_type) *
        (#pri_q <=# #npri)
      )
      @post (
        scope(Node: #n) *
        Queue(this, #pq_proto, #node_proto, #npri, #length + 1) *
        QueuePrototype(#pq_proto, #n, #node_proto) *
        (ret == $$empty)
      )

      @pre (
        (pri == #npri) *
        (val == #nval) *
        (0 <# #npri) *
        scope(Node: #n) *
        Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
        QueuePrototype(#pq_proto, #n, #node_proto) *
        types(#npri : $$number_type, #nval: $$string_type) *
        (#npri <# #pri_q)
      )
      @post (
        scope(Node: #n) *
        Queue(this, #pq_proto, #node_proto, #pri_q, #length + 1) *
        QueuePrototype(#pq_proto, #n, #node_proto) *
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
       Queue(this, #pq_proto, #node_proto, #pri_q, #length) *
       (0 <# #length) *
       QueuePrototype(#pq_proto, #n, #node_proto)
     )
     @post (
       (#length == #new_length + 1) *
       Queue(this, #pq_proto, #node_proto, #new_pri_q, #new_length) *
       QueuePrototype(#pq_proto, #n, #node_proto) *
       standardObject(#r) * dataField(#r, "pri", #pri_q) *
       dataField(#r, "val", #some_val) * (ret == #r)
     )

     @pre (
       Queue(this, #pq_proto, #node_proto, 0, 0) *
       QueuePrototype(#pq_proto, #n, #node_proto)
     )
     @posterr (
       Queue(this, #pq_proto, #node_proto, 0, 0) *
       QueuePrototype(#pq_proto, #n, #node_proto) *
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
