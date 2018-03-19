'use strict';

// ----------------------------------- _base.js -------------------------------

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

// ----------------------------------- arrays.js -----------------------------

/**
 * @namespace Contains various functions for manipulating arrays.
 */
buckets.arrays = {};

/**
 * Swaps the elements at the specified positions in the specified array.
 * @param {Array} array The array.
 * @param {number} i The index of the first element.
 * @param {number} j The index of second element.
 * @return {boolean} True if the array is defined and the indexes are valid.
 */
buckets.arrays.swap = function (array, i, j) {
    var temp;

    if (i < 0 || i >= array.length || j < 0 || j >= array.length) {
        return false;
    }
    temp = array[i];
    array[i] = array[j];
    array[j] = temp;
    return true;
};


// ------------------------------------ heap.js ------------------------------

/**
 * Creates an empty binary heap.
 * @class
 * <p>A heap is a binary tree that maintains the heap property:
 * Every node is less than or equal to each of its children. 
 * This implementation uses an array as the underlying storage.</p>
 * <p>If the inserted elements are custom objects, a compare function must be provided 
 * at construction time, otherwise the <=, === and >= operators are
 * used to compare elements.</p>
 * <p>Example:</p>
 * <pre>
 * function compare(a, b) {
 *  if (a is less than b by some ordering criterion) {
 *     return -1;
 *  } if (a is greater than b by the ordering criterion) {
 *     return 1;
 *  }
 *  // a must be equal to b
 *  return 0;
 * }
 * </pre>
 *
 * <p>To create a Max-Heap (greater elements on top) you can a provide a
 * reverse compare function.</p>
 * <p>Example:</p>
 *
 * <pre>
 * function reverseCompare(a, b) {
 *  if (a is less than b by some ordering criterion) {
 *     return 1;
 *  } if (a is greater than b by the ordering criterion) {
 *     return -1;
 *  }
 *  // a must be equal to b
 *  return 0;
 * }
 * </pre>
 *
 * @constructor
 * @param {function(Object,Object):number=} compareFunction Optional
 * function used to compare two elements. Must return a negative integer,
 * zero, or a positive integer as the first argument is less than, equal to,
 * or greater than the second.
 */
buckets.Heap = function (compareFunction) {

    /** 
     * @exports heap as buckets.Heap
     * @private
     */
    var heap = {},
        // Array used to store the elements of the heap.
        data = [],
        // Function used to compare elements.
        compare = compareFunction || buckets.defaultCompare;

    // Moves the node at the given index up to its proper place in the heap.
    function siftUp(index) {
        var parent;
        // Returns the index of the parent of the node at the given index.
        function parentIndex(nodeIndex) {
            return Math.floor((nodeIndex - 1) / 2);
        }

        parent = parentIndex(index);
        while (index > 0 && compare(data[parent], data[index]) > 0) {
            buckets.arrays.swap(data, parent, index);
            index = parent;
            parent = parentIndex(index);
        }
    }

    // Moves the node at the given index down to its proper place in the heap.
    function siftDown(nodeIndex) {
        var min;
        // Returns the index of the left child of the node at the given index.
        function leftChildIndex(nodeIndex) {
            return (2 * nodeIndex) + 1;
        }

        // Returns the index of the right child of the node at the given index.
        function rightChildIndex(nodeIndex) {
            return (2 * nodeIndex) + 2;
        }

        // Returns the index of the smaller child node if it exists, -1 otherwise.
        function minIndex(leftChild, rightChild) {
            if (rightChild >= data.length) {
                if (leftChild >= data.length) {
                    return -1;
                }
                return leftChild;
            }
            if (compare(data[leftChild], data[rightChild]) <= 0) {
                return leftChild;
            }
            return rightChild;
        }

        // Minimum child index
        min = minIndex(leftChildIndex(nodeIndex), rightChildIndex(nodeIndex));

        while (min >= 0 && compare(data[nodeIndex], data[min]) > 0) {
            buckets.arrays.swap(data, min, nodeIndex);
            nodeIndex = min;
            min = minIndex(leftChildIndex(nodeIndex), rightChildIndex(nodeIndex));
        }
    }

    /**
     * Retrieves but does not remove the root (minimum) element of the heap.
     * @return {*} The value at the root of the heap. Returns undefined if the
     * heap is empty.
     */
    heap.peek = function () {
        if (data.length > 0) {
            return data[0];
        }
        return undefined;
    };

    /**
     * Adds the given element into the heap.
     * @param {*} element The element.
     * @return True if the element was added or false if it is undefined.
     */
    heap.add = function (element) {
        if (buckets.isUndefined(element)) {
            return undefined;
        }
        data.push(element);
        siftUp(data.length - 1);
        return true;
    };

    /**
     * Retrieves and removes the root (minimum) element of the heap.
     * @return {*} The removed element or
     * undefined if the heap is empty.
     */
    heap.removeRoot = function () {
        var obj;
        if (data.length > 0) {
            obj = data[0];
            data[0] = data[data.length - 1];
            data.splice(data.length - 1, 1);
            if (data.length > 0) {
                siftDown(0);
            }
            return obj;
        }
        return undefined;
    };

    /**
     * Returns the number of elements in the heap.
     * @return {number} The number of elements in the heap.
     */
    heap.size = function () {
        return data.length;
    };

    return heap;
};

// --------------------------------- priorityqueue.js ------------------------

/**
 * Creates an empty priority queue.
 * @class <p>In a priority queue each element is associated with a "priority",
 * elements are dequeued in highest-priority-first order (the elements with the
 * highest priority are dequeued first). This implementation uses a binary 
 * heap as the underlying storage.</p>
 *
 * <p>If the inserted elements are custom objects, a compare function must be provided,
 * otherwise the <=, === and >= operators are used to compare object priority.</p>
 * <p>Example:</p>
 * <pre>
 * function compare(a, b) {
 *  if (a is less than b by some ordering criterion) {
 *     return -1;
 *  } if (a is greater than b by the ordering criterion) {
 *     return 1;
 *  }
 *  // a must be equal to b
 *  return 0;
 * }
 * </pre>
 * @constructor
 * @param {function(Object,Object):number=} compareFunction Optional
 * function used to compare two element priorities. Must return a negative integer,
 * zero, or a positive integer as the first argument is less than, equal to,
 * or greater than the second.
 */
 
buckets.PriorityQueue = function (compareFunction) {

    /** 
     * @exports pQueue as buckets.PriorityQueue
     * @private
     */
    var pQueue = {},
        // Reversed compare function
        compare = buckets.reverseCompareFunction(compareFunction),
        // Underlying storage
        heap = new buckets.Heap(compare);

    /**
     * Inserts the specified element into the priority queue.
     * @param {Object} element The element to insert.
     * @return {boolean} True if the element was inserted, or false if it's undefined.
     */
    pQueue.enqueue = function (element) {
        return heap.add(element);
    };

    /**
     * Retrieves and removes the highest priority element of the queue.
     * @return {*} The highest priority element of the queue,
     * or undefined if the queue is empty.
     */
    pQueue.dequeue = function () {
        var elem;
        if (heap.size() !== 0) {
            elem = heap.peek();
            heap.removeRoot();
            return elem;
        }
        return undefined;
    };

    /**
     * Returns the number of elements in the priority queue.
     * @return {number} The number of elements in the priority queue.
     */
    pQueue.size = function () {
        return heap.size();
    };

    return pQueue;
};

// ------------------------------ our test now -------------------------------

var queue = new buckets.PriorityQueue();

var x1 = symb_number(x1); // 2
var x2 = symb_number(x2); // 1
// var x3 = symb_number(x3); // 3
// var x1 = 2;
// var x2 = 1;
// var x3 = 3;

Assume (x2 < x1); // x1 = 2, x2 = 3, x3 = 1

queue.enqueue(x1);
queue.enqueue(x2);
// queue.enqueue(x3);

var l0 = queue.size();
var y1 = queue.dequeue(); // y1 = 3 = x2
var l1 = queue.size();
var y2 = queue.dequeue(); // y2 = 2 = x1
var l2 = queue.size();
// var y3 = queue.dequeue(); // y3 = 1 = x3

// console.log(y1);
// console.log(y2);
// console.log(y3);

Assert((l0 = 2) and (l1 = 1) and (l2 = 0) and (y1 = x2) and (y2 = x1));