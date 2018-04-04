'use strict';

/**
 * Top level namespace for Buckets,
 * a JavaScript data structure library.
 * @name buckets
 */
var buckets = {};

/**
 * Default function to compare element order.
 * @function
 * @private
 */
buckets.defaultCompare = function (a, b) {
    if (a < b) {
        return -1;
    }
    if (a === b) {
        return 0;
    }
    return 1;
};

/**
 * Default function to test equality.
 * @function
 * @private
 */
buckets.defaultEquals = function (a, b) {
    return a === b;
};

/**
 * Default function to convert an object to a string.
 * @function
 * @private
 */
buckets.defaultToString = function (item) {
    if (item === null) {
        return 'BUCKETS_NULL';
    }
    if (buckets.isUndefined(item)) {
        return 'BUCKETS_UNDEFINED';
    }
    if (buckets.isString(item)) {
        return item;
    }
    return item.toString();
};

/**
 * Checks if the given argument is a function.
 * @function
 * @private
 */
buckets.isFunction = function (func) {
    return (typeof func) === 'function';
};

/**
 * Checks if the given argument is undefined.
 * @function
 * @private
 */
buckets.isUndefined = function (obj) {
    return obj === undefined;
};

/**
 * Checks if the given argument is a string.
 * @function
 * @private
 */
buckets.isString = function (obj) {
    return Object.prototype.toString.call(obj) === '[object String]';
};

/**
 * Reverses a compare function.
 * @function
 * @private
 */
buckets.reverseCompareFunction = function (compareFunction) {
    if (!buckets.isFunction(compareFunction)) {
        return function (a, b) {
            if (a < b) {
                return 1;
            }
            if (a === b) {
                return 0;
            }
            return -1;
        };
    }
    return function (d, v) {
        return compareFunction(d, v) * -1;
    };

};

/**
 * Returns an equal function given a compare function.
 * @function
 * @private
 */
buckets.compareToEquals = function (compareFunction) {
    return function (a, b) {
        return compareFunction(a, b) === 0;
    };
};

// ----------------------------- linkedlist.js --------------------------------

/**
 * Creates an empty Linked List.
 * @class A linked list is a sequence of items arranged one after 
 * another. The size is not fixed and it can grow or shrink 
 * on demand. One of the main benefits of a linked list is that 
 * you can add or remove elements at both ends in constant time. 
 * One disadvantage of a linked list against an array is 
 * that it doesn’t provide constant time random access.
 * @constructor
 */
buckets.LinkedList = function () {

    /** 
     * @exports list as buckets.LinkedList
     * @private
     */
    var list = {},
        // Number of elements in the list
        nElements = 0,
        // First node in the list
        firstNode,
        // Last node in the list
        lastNode;

    // Returns the node at the specified index.
    function nodeAtIndex(index) {
        var node, i;
        if (index < 0 || index >= nElements) {
            return undefined;
        }
        if (index === (nElements - 1)) {
            return lastNode;
        }
        node = firstNode;
        for (i = 0; i < index; i += 1) {
            node = node.next;
        }
        return node;
    }

    /**
     * Adds an element to the list.
     * @param {Object} item Element to be added.
     * @param {number=} index Optional index to add the element. If no index is specified
     * the element is added to the end of the list.
     * @return {boolean} True if the element was added or false if the index is invalid
     * or if the element is undefined.
     */
    list.add = function (item, index) {
        var newNode, prev;

        if (buckets.isUndefined(index)) {
            index = nElements;
        }
        if (index < 0 || index > nElements || buckets.isUndefined(item)) {
            return false;
        }
        newNode = {
            element: item,
            next: undefined
        };
        if (nElements === 0) {
            // First node in the list.
            firstNode = newNode;
            lastNode = newNode;
        } else if (index === nElements) {
            // Insert at the end.
            lastNode.next = newNode;
            lastNode = newNode;
        } else if (index === 0) {
            // Change first node.
            newNode.next = firstNode;
            firstNode = newNode;
        } else {
            prev = nodeAtIndex(index - 1);
            newNode.next = prev.next;
            prev.next = newNode;
        }
        nElements += 1;
        return true;
    };

    /**
     * Returns the first element in the list.
     * @return {*} The first element in the list or undefined if the list is
     * empty.
     */
    list.first = function () {
        if (firstNode !== undefined) {
            return firstNode.element;
        }
        return undefined;
    };

    /**
     * Returns the last element in the list.
     * @return {*} The last element in the list or undefined if the list is
     * empty.
     */
    list.last = function () {
        if (lastNode !== undefined) {
            return lastNode.element;
        }
        return undefined;
    };

    /**
     * Returns the element at the specified position in the list.
     * @param {number} index Desired index.
     * @return {*} The element at the given index or undefined if the index is
     * out of bounds.
     */
    list.elementAtIndex = function (index) {
        var node = nodeAtIndex(index);
        if (node === undefined) {
            return undefined;
        }
        return node.element;
    };


    /**
     * Returns the index of the first occurrence of the
     * specified element, or -1 if the list does not contain the element.
     * <p>If the elements inside the list are
     * not comparable with the === operator, a custom equals function should be
     * provided to perform searches, that function must receive two arguments and
     * return true if they are equal, false otherwise. Example:</p>
     *
     * <pre>
     * var petsAreEqualByName = function(pet1, pet2) {
     *  return pet1.name === pet2.name;
     * }
     * </pre>
     * @param {Object} item Element to search for.
     * @param {function(Object,Object):boolean=} equalsFunction Optional
     * function used to check if two elements are equal.
     * @return {number} The index in the list of the first occurrence
     * of the specified element, or -1 if the list does not contain the
     * element.
     */
    list.indexOf = function (item, equalsFunction) {
        var equalsF = equalsFunction || buckets.defaultEquals,
            currentNode = firstNode,
            index = 0;
        if (buckets.isUndefined(item)) {
            return -1;
        }

        while (currentNode !== undefined) {
            if (equalsF(currentNode.element, item)) {
                return index;
            }
            index += 1;
            currentNode = currentNode.next;
        }
        return -1;
    };

    /**
     * Returns true if the list contains the specified element.
     * <p>If the elements inside the list are
     * not comparable with the === operator, a custom equals function should be
     * provided to perform searches, that function must receive two arguments and
     * return true if they are equal, false otherwise. Example:</p>
     *
     * <pre>
     * var petsAreEqualByName = function(pet1, pet2) {
     *  return pet1.name === pet2.name;
     * }
     * </pre>
     * @param {Object} item Element to search for.
     * @param {function(Object,Object):boolean=} equalsFunction Optional
     * function used to check if two elements are equal.
     * @return {boolean} True if the list contains the specified element, false
     * otherwise.
     */
    list.contains = function (item, equalsFunction) {
        return (list.indexOf(item, equalsFunction) >= 0);
    };

    /**
     * Removes the first occurrence of the specified element in the list.
     * <p>If the elements inside the list are
     * not comparable with the === operator, a custom equals function should be
     * provided to perform searches, that function must receive two arguments and
     * return true if they are equal, false otherwise. Example:</p>
     * <pre>
     * var petsAreEqualByName = function(pet1, pet2) {
     *  return pet1.name === pet2.name;
     * }
     * </pre>
     * @param {Object} item Element to be removed from the list, if present.
     * @return {boolean} True if the list contained the specified element.
     */
    list.remove = function (item, equalsFunction) {
        var equalsF = equalsFunction || buckets.defaultEquals,
            currentNode = firstNode,
            previous;

        if (nElements < 1 || buckets.isUndefined(item)) {
            return false;
        }

        while (currentNode !== undefined) {

            if (equalsF(currentNode.element, item)) {

                if (currentNode === firstNode) {
                    firstNode = firstNode.next;
                    if (currentNode === lastNode) {
                        lastNode = undefined;
                    }
                } else if (currentNode === lastNode) {
                    lastNode = previous;
                    previous.next = currentNode.next;
                    currentNode.next = undefined;
                } else {
                    previous.next = currentNode.next;
                    currentNode.next = undefined;
                }
                nElements = nElements - 1;
                return true;
            }
            previous = currentNode;
            currentNode = currentNode.next;
        }
        return false;
    };

    /**
     * Removes all the elements from the list.
     */
    list.clear = function () {
        firstNode = undefined;
        lastNode = undefined;
        nElements = 0;
    };

    /**
     * Returns true if the list is equal to another list.
     * Two lists are equal if they have the same elements in the same order.
     * @param {buckets.LinkedList} other The other list.
     * @param {function(Object,Object):boolean=} equalsFunction Optional
     * function to check if two elements are equal. If the elements in the lists
     * are custom objects you should provide a custom equals function, otherwise
     * the === operator is used to check equality between elements.
     * @return {boolean} true if the list is equal to the given list.
     */
    list.equals = function (other, equalsFunction) {
        var eqf = equalsFunction || buckets.defaultEquals,
            isEqual = true,
            node = firstNode;

        if (buckets.isUndefined(other) || typeof other.elementAtIndex !== 'function') {
            return false;
        }
        if (list.size() !== other.size()) {
            return false;
        }

        other.forEach(function (element) {
            isEqual = eqf(element, node.element);
            node = node.next;
            return isEqual;
        });

        return isEqual;
    };

    /**
     * Removes the element at the specified position in the list.
     * @param {number} index Given index.
     * @return {*} Removed element or undefined if the index is out of bounds.
     */
    list.removeElementAtIndex = function (index) {
        var element, previous;

        if (index < 0 || index >= nElements) {
            return undefined;
        }

        if (nElements === 1) {
            //First node in the list.
            element = firstNode.element;
            firstNode = undefined;
            lastNode = undefined;
        } else {
            previous = nodeAtIndex(index - 1);
            if (previous === undefined) {
                element = firstNode.element;
                firstNode = firstNode.next;
            } else if (previous.next === lastNode) {
                element = lastNode.element;
                lastNode = previous;
            }
            if (previous !== undefined) {
                element = previous.next.element;
                previous.next = previous.next.next;
            }
        }
        nElements -= 1;
        return element;
    };

    /**
     * Executes the provided function once per element present in the list in order.
     * @param {function(Object):*} callback Function to execute, it is
     * invoked with one argument: the element value, to break the iteration you can
     * optionally return false inside the callback.
     */
    list.forEach = function (callback) {
        var currentNode = firstNode;
        while (currentNode !== undefined) {
            if (callback(currentNode.element) === false) {
                break;
            }
            currentNode = currentNode.next;
        }
    };

    /**
     * Reverses the order of the elements in the linked list (makes the last
     * element first, and the first element last).
     * @memberOf buckets.LinkedList
     */
    list.reverse = function () {
        var current = firstNode,
            previous,
            temp;
        while (current !== undefined) {
            temp = current.next;
            current.next = previous;
            previous = current;
            current = temp;
        }
        temp = firstNode;
        firstNode = lastNode;
        lastNode = temp;
    };


    /**
     * Returns an array containing all the elements in the list in proper
     * sequence.
     * @return {Array.<*>} An array containing all the elements in the list,
     * in proper sequence.
     */
    list.toArray = function () {
        var result = [];
        list.forEach(function (element) {
            result.push(element);
        });
        return result;
    };

    /**
     * Returns the number of elements in the list.
     * @return {number} The number of elements in the list.
     */
    list.size = function () {
        return nElements;
    };

    /**
     * Returns true if the list contains no elements.
     * @return {boolean} true if the list contains no elements.
     */
    list.isEmpty = function () {
        return nElements <= 0;
    };

    return list;
};


// -------------------------------- queue.js ----------------------------------

/**
 * Creates an empty queue.
 * @class A queue is a First-In-First-Out (FIFO) data structure, the first
 * element added to the queue will be the first one to be removed. This
 * implementation uses a linked list as the underlying storage.
 * @constructor
 */
buckets.Queue = function () {

    /** 
     * @exports queue as buckets.Queue
     * @private
     */
    var queue = {},
        // Underlying list containing the elements.
        list = new buckets.LinkedList();

    /**
     * Inserts the specified element into the end of the queue.
     * @param {Object} elem The element to insert.
     * @return {boolean} True if the element was inserted, or false if it's undefined.
     */
    queue.enqueue = function (elem) {
        return list.add(elem);
    };

    /**
     * Inserts the specified element into the end of the queue. Equivalent to enqueue.
     * @param {Object} elem The element to insert.
     * @return {boolean} True if the element was inserted, or false if it's undefined.
     */
    queue.add = function (elem) {
        return list.add(elem);
    };

    /**
     * Retrieves and removes the head of the queue.
     * @return {*} The head of the queue, or undefined if the queue is empty.
     */
    queue.dequeue = function () {
        var elem;
        if (list.size() !== 0) {
            elem = list.first();
            list.removeElementAtIndex(0);
            return elem;
        }
        return undefined;
    };

    /**
     * Retrieves, but does not remove, the head of the queue.
     * @return {*} The head of the queue, or undefined if the queue is empty.
     */
    queue.peek = function () {
        if (list.size() !== 0) {
            return list.first();
        }
        return undefined;
    };

    /**
     * Returns the number of elements in the queue.
     * @return {number} The number of elements in the queue.
     */
    queue.size = function () {
        return list.size();
    };

    /**
     * Returns true if the queue contains the specified element.
     * <p>If the elements inside the queue are
     * not comparable with the === operator, a custom equals function should be
     * provided to perform searches, the function must receive two arguments and
     * return true if they are equal, false otherwise. Example:</p>
     *
     * <pre>
     * var petsAreEqualByName = function(pet1, pet2) {
     *  return pet1.name === pet2.name;
     * }
     * </pre>
     * @param {Object} elem Element to search for.
     * @param {function(Object,Object):boolean=} equalsFunction Optional
     * function to check if two elements are equal.
     * @return {boolean} True if the queue contains the specified element,
     * false otherwise.
     */
    queue.contains = function (elem, equalsFunction) {
        return list.contains(elem, equalsFunction);
    };

    /**
     * Checks if the queue is empty.
     * @return {boolean} True if and only if the queue contains no items.
     */
    queue.isEmpty = function () {
        return list.size() <= 0;
    };

    /**
     * Removes all the elements from the queue.
     */
    queue.clear = function () {
        list.clear();
    };

    /**
     * Executes the provided function once per each element present in the queue in
     * FIFO order.
     * @param {function(Object):*} callback Function to execute, it's
     * invoked an element as argument, to break the iteration you can
     * optionally return false inside the callback.
     */
    queue.forEach = function (callback) {
        list.forEach(callback);
    };

    /**
     * Returns an array containing all the elements in the queue in FIFO
     * order.
     * @return {Array.<*>} An array containing all the elements in the queue
     * in FIFO order.
     */
    queue.toArray = function () {
        return list.toArray();
    };

    /**
     * Returns true if the queue is equal to another queue.
     * Two queues are equal if they have the same elements in the same order.
     * @param {buckets.Queue} other The other queue.
     * @param {function(Object,Object):boolean=} equalsFunction Optional
     * function to check if two elements are equal. If the elements in the queues
     * are custom objects you should provide a custom equals function, otherwise
     * the === operator is used to check equality between elements.
     * @return {boolean} True if the queue is equal to the given queue.
     */
    queue.equals = function (other, equalsFunction) {
        var eqf, isEqual, thisElement;
        if (buckets.isUndefined(other) || typeof other.dequeue !== 'function') {
            return false;
        }
        if (queue.size() !== other.size()) {
            return false;
        }
        eqf = equalsFunction || buckets.defaultEquals;
        isEqual = true;
        other.forEach(function (element) {
            thisElement = queue.dequeue();
            queue.enqueue(thisElement);
            isEqual = eqf(thisElement, element);
            return isEqual;
        });
        return isEqual;
    };

    return queue;
};

// ------------------------------- our tests ----------------------------------

// modeling the tests from test/queue-test.js

var queue = new buckets.Queue();

var x1 = symb_number(x1); // 1
var x2 = symb_number(x2); // 2
var x3 = symb_number(x3); // 3
Assume((x1 < x2) and (x2 < x3));

function createQueue() {
  queue.enqueue(x1);
  queue.enqueue(x2);
  queue.enqueue(x3);
}

// TEST 1
/// this one OK
//it('size gives the right value', function () {
var queue = new buckets.Queue();
var size = queue.size();
Assert(size = 0);
createQueue();
var size = queue.size();
Assert(size = 3);
var x4 = symb_number(x4);
queue.enqueue(x4);
var size = queue.size();
Assert(size = 4);
queue.dequeue();
var size = queue.size();
Assert(size = 3);
queue.clear();
var size = queue.size();
Assert(size = 0);
queue.clear();

// TEST 2
/// this one OK
// it('enqueue inserts elements to the queue', function () {
var queue = new buckets.Queue();
var head;
createQueue();
head = queue.dequeue();
Assert(head = x1);
queue.dequeue();
head = queue.dequeue();
Assert(head = x3);
var isEmpty = queue.isEmpty();
Assert(isEmpty);
head = queue.dequeue();
Assert(head = $$undefined);
queue.clear();


// TEST 3
/// this one OK
// it('peek returns the first element or undefined', function () {
var queue = new buckets.Queue();
var head, head2;
createQueue();
head = queue.peek();
Assert(head = x1);
head2 = queue.dequeue();
Assert(head = head2);
head = queue.peek();
Assert(head = x2);
queue.clear();
head = queue.peek();
Assert(head = $$undefined);
queue.clear();


// TEST 4
/// this one OK (not symbolic)
// it('forEach gives the elements in order', function () {
var queue = new buckets.Queue();
var i;
queue.forEach(function (e) {
    Assert($$f); // should not enter here
});

for (i = 0; i < 10; i += 1) {
    queue.add(i);
}

i = 0;
queue.forEach(function (e) {
    Assert(e = i);
    i += 1;
});
queue.clear();


// TEST 5
/// this one OK
// it('forEach can be interrupted', function () {
var queue = new buckets.Queue();
var array = [0, 1, 2, 3, 4],
    b = [],
    i;
for (i = 0; i < 5; i += 1) {
    queue.add(i);
}
queue.forEach(function (e) {
    b.push(e);
    if (e === 3) {
        return false;
    }
});

var array2 = [0, 1, 2, 3];

var s1 = b.length;
var s2 = array2.length;
Assert(s1 = s2);
var i;
for (i = 0; i < s1; i++) {
  var y1 = b[i];
  var y2 = array2[i];
  Assert(y1 = y2);
}
queue.clear();

// TEST 6
/// this one OK
// it('contains returns true for inserted items', function () {
var queue = new buckets.Queue();
createQueue();
var res = queue.contains(x1);
Assert(res);
queue.clear();


// TEST 7
/// this one ok
// it('contains returns false for non-inserted items', function () {
var queue = new buckets.Queue();
createQueue();
var x4 = symb_number(x4);
Assume((not (x4 = x1)) and (not (x4 = x2)) and (not (x4 = x3)));
var res1 = queue.contains(x4);
Assert(not res1);
var res2 = queue.contains(undefined);
Assert(not res2);
queue.clear();


// TEST 8
/// this one OK
// it('toArray gives the elements in order', function () {
var queue = new buckets.Queue();
var res = queue.toArray().length;
Assert(res = 0);

queue.add(5);
var arr = queue.toArray();
var res = arr[0];
var len = arr.length;
Assert(res = 5);
Assert(len = 1);

queue.add(8);
arr = queue.toArray();
var res1 = arr[0];
var res2 = arr[1];
var len = arr.length;
Assert(res1 = 5);
Assert(res2 = 8);
Assert(len = 2);
queue.clear();

// TEST 9
/// this one OK
//it('equals returns true only if queues have the same elements in order', function () {
var queue = new buckets.Queue();
var queue2 = new buckets.Queue();
queue.add(1);
queue.add(2);

queue2.add(1);
queue2.add(2);

var res = queue.equals(queue2);
Assert(res);
queue2.clear();
queue2.add(2);
queue2.add(1);
var res = queue.equals(queue2);
Assert(not res);
var res = queue.equals([1, 2]);
Assert(not res);
queue.clear();

