
var PriorityQueue = (function () {

	var counter = 0;

	var Node = function (pri, val) {
		this.pri = pri; 
		this.val = val; 
		this.next = null;
		counter++
	}

	Node.prototype.insert = function (nl) {
		if (nl === null) {
		   return this
		}
		
		if (this.pri > nl.pri) {
		   return this
		}
		
		var tmp = this.insert (nl.next);
		nl.next = tmp;
		return nl
	}; 

	var listLength = function (lst) {
		if (lst == null) { 
			return 0 
		} else { 
			return 1 + listLength (lst.next)
		}
	}; 

	var PQ = function () {
		this._head = null;
	};

	
	PQ.prototype.enqueue = function(pri, val) {
		var n = new Node(pri, val);
		this._head = n.insert(this._head);
	};

   PQ.prototype.dequeue = function () {
      if (this._head === null) {
        throw new Error("Queue is empty");
      }

	  counter--;
      var first = this._head;
      this._head = this._head.next;
      return {pri: first.pri, val: first.val};
   };


   PQ.prototype.length = function () { 
      return listLength(this._head); 
   }; 

   return PQ;
})();

var q, r, len; 

var p1 = symb_number (p1);
var s1 = symb_string (s1);
var p2 = symb_number (p2);
var s2 = symb_string (s2);
var p3 = symb_number (p3);
var s3 = symb_number (s3);

q = new PriorityQueue();
q.enqueue (p1, s1); 
q.enqueue (p2, s2); 
q.enqueue (p3, s3); 
r = (q.dequeue()).val;
len = q.length(); 
Assert (len = 2); 
r


