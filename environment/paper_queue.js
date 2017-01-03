/**
Predicate Definitions

pred Object (l, proto) :
    types (l : $$object_type) *
	((l, "@proto") -> proto) *
	((l, "@class") -> "Object") *
	((l, "@extensible") -> $$t)

NodePrototype(np) :
	StandardObject(np) * 
	dataField(np, "push", #push) *
	fun_obj(push, #push, #push_proto)

Node(n, pri, elt, next, node_proto) :
	Object(n, node_proto) * 
	dataField(n, "pri",  pri) * 
    dataField(n, "elt",  elt) * 
    dataField(n, "next", next)

Queue(q, node_proto, max_pri) :
   (q == $$null) * (max == -1),

   Node(q, #pri, #elt, #next, node_proto) * Queue(#next, node_proto, #pri)
      * (#pri <= max_pri)
*/

/**
   @id  newNodeConstructor
   @rec false

   @pre  (emp)
   @post (((ret, "nc") -> #nc) * ((ret, "gc") -> #gc) *
               fun_obj(Node, #nc, #node_proto) *
               fun_obj(getCounter, #gc, #gc_proto) *
               NodePrototype(#node_proto))
*/
function newNodeConstructor () {
   var counter = 0;

   /**
      @id  Node
      @rec false

      @pre (
      		scope(counter: #c) * types(#c : $$int_type) *
      		(pri == #pri) * (elt == #elt) * types(#pri: $$int_type, #elt: $$string_type) *  
      		((this, "pri") -> None) * ((this, "elt") -> None) * ((this, "next") -> None) * 
      		Object(this, #node_proto) * NodePrototype(#node_proto)
      )
      @post (
      		 scope(counter: #c + 1) *
      		 Node(this, #pri, #elt, $$null, #node_proto) *
      		 NodePrototype(#node_proto))
   */
   var Node = function (pri, elt) {
      this.pri = pri; this.elt = elt; this.next = null;
      counter++
   }


   /**
      @id  push
      @rec true

      @pre  ((q == #q) * Node(this, #pri, #elt, $$null, #node_proto)
               * Queue(#q, #node_proto, #pri_q) * NodePrototype(#node_proto)
               * scope(Node: #node) * fun_object (Node, #nc, #node_proto))
      @post (Queue(ret, #node_proto, #pri_f) * NodePrototype(#node_proto))
   */
   Node.prototype.push = function (q) {
      /**
         @unfold Node(this, $$null, #node_proto)
         @unfold Queue(#q, #node_proto, #pri_q)
      */
      if ((!(q instanceof Node)) || !q) {
         /**
            @fold Queue(this, #node_proto, #pri)
         */
         return this
      } else if (this.pri >= q.pri) {
         this.next = q;
         /**
            @fold Queue(#q, #node_proto, #pri_q)
            @fold Queue(this, #node_proto, #pri)
         */
         return this
      } else {
         /**
            @fold Node(this, #pri, #elt, $$null, #node_proto)
         */
         var tmp = this.push (q.next);
         q.next = tmp;
         /**
            @fold Queue(#q, #node_proto, #pri_q)
         */
         return q
      }
   }


   /**
   	@id  getCounter
   	@rec false

   	@pre  (scope(counter: #c) * types(#c : $$int_type))
   	@post (scope(counter: #c) * (ret == #c))
   */
   var getCounter = function () { return counter; };
   return {nc: Node, gc: getCounter }
}


var o = newNodeConstructor ();
var Node = o.nc;
var getCounter = o.getCounter;
