
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
		   this.next = nl;
		   return this
		}
		
		var tmp = this.insert (nl.next);
		nl.next = tmp;
		return nl
	}

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

   return PQ;
})();

var q, r;

var p1 = symb_number (p1);
var s1 = symb_string (s1);
var p2 = symb_number (p2);
var s2 = symb_string (s2);
var p3 = symb_number (p3);
var s3 = symb_number (s3);
q = new PriorityQueue();

assume ((not (p1 = p2)) and (not (p2 = p3)) and (not (p1 = p3)));
assume ((p1 < 0) and (p2 < 0) and (0 < p3))
q.enqueue (p1, s1); 
q.enqueue (p2, s2); 
q.enqueue (p3, s3); 
r = (q.dequeue()).val;
assert (r = s3); 
r


