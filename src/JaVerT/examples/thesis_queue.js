/**

@pred Object (l, proto) :
	types (l : $$object_type) *
	((l, "@proto") -> proto) *
	((l, "@class") -> "Object") *
	((l, "@extensible") -> $$t);

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

  @pred Queue(q, node_proto, max_pri, length) :
  	(q == $$null) * (max_pri == 0) * (length == 0) * types(max_pri : $$number_type, length : $$number_type),

  	Node(q, max_pri, #val, #next, node_proto) * (0 <# max_pri) *
  	Queue(#next, node_proto, #pri, #len_q) * (#pri <=# max_pri) * (length == #len_q + 1) *
  	types(q : $$object_type, node_proto : $$object_type, #pri : $$number_type, max_pri : $$number_type, length : $$number_type, #len_q : $$number_type);
*/


/* @id Module */
var PriorityQueue = (function () {

  /**
  	@id  Node

  	@pre (
  	   	(pri == #pri) * (val == #val) * types(#pri: $$number_type, #val: $$string_type) *
  	   	(0 <# #pri) *
  	   	((this, "pri") -> None) * ((this, "val") -> None) * ((this, "next") -> None) *
  	    ((this, "insertToQueue") -> None) *
  	   	Object(this, #node_proto) * NodePrototype(#node_proto, #insert_loc)
  	)

  	@post (
  	   		Node(this, #pri, #val, $$null, #node_proto) *
  	   		NodePrototype(#node_proto, #insert_loc))
  */
   var Node = function (pri, val) {
      this.pri = pri; this.val = val; this.next = null;
   }

   /**
   	@id  insertToQueue

    @pre (
      (q == #q) *
      Queue(#q, #node_proto, #pri_q, #length) *
      Node(this, #npri, #nval, $$null, #node_proto) *
      NodePrototype(#node_proto, #insert_loc) *
      (#pri_q <=# #npri) *
      types(#npri : $$number_type, #pri_q : $$number_type, #length : $$number_type)
    )
    @post (
      Queue(this, #node_proto, #npri, #length + 1) *
      (ret == this) *
      NodePrototype(#node_proto, #insert_loc)
    )

    @pre (
   		(q == #q) *
   		Queue(#q, #node_proto, #pri_q, #length) *
   		Node(this, #npri, #nval, $$null, #node_proto) *
   		NodePrototype(#node_proto, #insert_loc) *
   		(#npri <# #pri_q) *
   		types(#npri : $$number_type, #pri_q : $$number_type, #q : $$object_type)
   	)
   	@post (
   		Queue(#q, #node_proto, #pri_q, #length + 1) * (ret == #q) *
   		NodePrototype(#node_proto, #insert_loc) * types (#q : $$object_type)
   	)


  */
   Node.prototype.insertToQueue = function (q) {
      /** @unfold Queue(#q, #node_proto, #pri_q, #length) */
      if (q === null) {
         /** @fold Queue(this, #node_proto, #npri, #length + 1) */
         return this
      }

      if (this.pri >= q.pri) {
         this.next = q;
         /** @fold Queue(this, #node_proto, #npri, #length + 1) */
         return this
      }

      var tmp = this.insertToQueue (q.next);
      q.next = tmp;
      /** @fold Queue(#q, #node_proto, #pri_q, #length + 1) */
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
