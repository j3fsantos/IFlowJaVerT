/**************************************************
 * Linked list node class
 *
 * Internal private class to represent a node within
 * a linked list.  Each node has a 'data' property and
 * a pointer the previous node and the next node in the list.
 *
 * Since the 'Node' function is not assigned to
 * module.exports it is not visible outside of this
 * file, therefore, it is private to the LinkedList
 * class.
 *
 ***************************************************/

/**
 * Creates a node object with a data property and pointer
 * to the next node
 *
 * @constructor
 * @param {object|number|string} data The data to initialize with the node
 *
 * @pre  (standardObject(this) * ((this, "data") -> None)  * ((this, "next") -> None) * ((this, "prev") -> None) * types(data : $$number_type))
 * @post (standardObject(this) * dataField(this, "data", data) * dataField(this, "next", $$null) * dataField(this, "prev", $$null))
 */
function Node(data) {
    this.data = data;
    this.next = null;
    this.prev = null;
}

/* Functions attached to the Node prototype.  All node instances will
 * share these methods, meaning there will NOT be copies made for each
 * instance.  This will be a huge memory savings since there will likely
 * be a large number of individual nodes.
 */
Node.prototype = {

    /**
     * Returns whether or not the node has a pointer to the next node
     *
     * @returns {boolean} true if there is a next node; false otherwise
     *
     */
    hasNext: function() {
        return (this.next !== null);
    },

    /**
     * Returns whether or not the node has a pointer to the previous node
     *
     * @returns {boolean} true if there is a previous node; false otherwise
     */
    hasPrev: function() {
        return (this.prev !== null);
    },

    /**
     * Returns the data of the the node
     *
     * @returns {object|string|number} the data of the node
     */
    getData: function() {
        return this.data;
    }
};

/**************************************************
 * Iterator class
 *
 * Represents an instantiation of an iterator to be used
 * within a linked list.  The iterator will provide the ability
 * to iterate over all nodes in a list by keeping track of the
 * postition of a 'currentNode'.  This 'currentNode' pointer
 * will keep state until a reset() operation is called at which
 * time it will reset to point the head of the list.
 *
 * Even though this iterator class is inextricably linked
 * (no pun intended) to a linked list instatiation, it was removed
 * from within the linked list code to adhere to the best practice
 * of separation of concerns.
 *
 ***************************************************/

/**
 * Creates an iterator instance to iterate over the linked list provided.
 *
 * @constructor
 * @param {object} theList the linked list to iterate over
 */
function Iterator(theList) {
    this.list = theList || null;

    // a pointer the current node in the list that will be returned.
    // initially this will be null since the 'list' will be empty
    this.currentNode = null;
}

/* Functions attached to the Iterator prototype.  All iterator instances
 * will share these methods, meaning there will NOT be copies made for each
 * instance.
 */
Iterator.prototype = {

    /**
     * Returns the next node in the iteration.
     *
     * @returns {object} the next node in the iteration.
     */
    next: function() {
        var current = this.currentNode;
        // a check to prevent error if randomly calling next() when
        // iterator is at the end of the list, meaining the currentNode
        // will be pointing to null.
        //
        // When this function is called, it will return the node currently
        // assigned to this.currentNode and move the pointer to the next
        // node in the list (if it exists)
        if (this.currentNode !== null) {
            this.currentNode = this.currentNode.next;
        }

        return current;
    },

    /**
     * Determines if the iterator has a node to return
     *
     * @returns true if the iterator has a node to return, false otherwise
     */
    hasNext: function() {
        return this.currentNode !== null;
    },

    /**
     * Resets the iterator to the beginning of the list.
     */
    reset: function() {
        this.currentNode = this.list.getHeadNode();
    },

    /**
     * Returns the first node in the list and moves the iterator to
     * point to the second node.
     *
     * @returns the first node in the list
     */
    first: function() {
        this.reset();
        return this.next();
    },

    /**
     * Sets the list to iterate over
     *
     * @param {object} theList the linked list to iterate over
     */
    setList: function(theList) {
        this.list = theList;
        this.reset();
    }
};

/**************************************************
 * Doubly linked list class
 *
 * Implementation of a doubly linked list data structure.  This
 * implementation provides the general functionality of adding nodes to
 * the front or back of the list, as well as removing node from the front
 * or back.  This functionality enables this implemention to be the
 * underlying data structure for the more specific stack or queue data
 * structure.
 *
 ***************************************************/

/**
 * Creates a LinkedList instance.  Each instance has a head node, a tail
 * node and a size, which represents the number of nodes in the list.
 *
 * @constructor
 */
function DoublyLinkedList() {
    this.head = null;
    this.tail = null;
    this.size = 0;

    // add iterator as a property of this list to share the same
    // iterator instance with all other methods that may require
    // its use.  Note: be sure to call this.iterator.reset() to
    // reset this iterator to point the head of the list.
    this.iterator = new Iterator(this);
}

/* Functions attached to the Linked-list prototype.  All linked-list
 * instances will share these methods, meaning there will NOT be copies
 * made for each instance.  This will be a huge memory savings since there
 * may be several different linked lists.
 */
DoublyLinkedList.prototype = {

    /**
     * Creates a new Node object with 'data' assigned to the node's data
     * property
     *
     * @param {object|string|number} data The data to initialize with the
     *                                    node
     * @returns {object} Node object intialized with 'data'
     */
    createNewNode: function(data) {
        return new Node(data);
    },

    /**
     * Returns the first node in the list, commonly referred to as the
     * 'head' node
     *
     * @returns {object} the head node of the list
     */
    getHeadNode: function() {
        return this.head;
    },

    /**
     * Returns the last node in the list, commonly referred to as the
     * 'tail'node
     *
     * @returns {object} the tail node of the list
     */
    getTailNode: function() {
        return this.tail;
    },

    /**
     * Determines if the list is empty
     *
     * @returns {boolean} true if the list is empty, false otherwise
     */
    isEmpty: function() {
        return (this.size === 0);
    },

    /**
     * Returns the size of the list, or number of nodes
     *
     * @returns {number} the number of nodes in the list
     */
    getSize: function() {
        return this.size;
    },

    /**
     * Clears the list of all nodes/data
     */
    clear: function () {
        while (!this.isEmpty()) {
            this.remove();
        }
    },

    //################## INSERT methods ####################

    /**
     * Inserts a node with the provided data to the end of the list
     *
     * @param {object|string|number} data The data to initialize with the
     *                                    node
     * @returns {boolean} true if insert operation was successful
     */
    insert: function(data) {
        var newNode = this.createNewNode(data);
        if (this.isEmpty()) {
            this.head = this.tail = newNode;
        } else {
            this.tail.next = newNode;
            newNode.prev = this.tail;
            this.tail = newNode;
        }
        this.size += 1;

        return true;
    },

    /**
     * Inserts a node with the provided data to the front of the list
     *
     * @param {object|string|number} data The data to initialize with the
     *                                    node
     * @returns {boolean} true if insert operation was successful
     */
    insertFirst: function(data) {
        if (this.isEmpty()) {
            this.insert(data);
        } else {
            var newNode = this.createNewNode(data);

            newNode.next = this.head;
            this.head.prev = newNode;
            this.head = newNode;

            this.size += 1;
        }

        return true;
    },

    /**
     * Inserts a node with the provided data at the index indicated.
     *
     * @param {number} index The index in the list to insert the new node
     * @param {object|string|number} data The data to initialize with the node
     */
    insertAt: function (index, data) {
        var current = this.getHeadNode(),
            newNode = this.createNewNode(data),
            previous = null,
            position = 0;

        // check for index out-of-bounds
        if (index < 0 || index > this.getSize() - 1) {
            return false;
        }

        // if index is 0, we just need to insert the first node
        if (index === 0) {
            this.insertFirst(data);
            return true;
        }

        while (position < index) {
            previous = current;
            current = current.next;
            position += 1;
        }

        current.prev.next = newNode;
        newNode.prev = current.prev;
        current.prev = newNode;
        newNode.next = current;

        this.size += 1;

        return true;
    },

    /**
     * Inserts a node before the first node containing the provided data
     *
     * @param {object|string|number} nodeData The data of the node to
     *         find to insert the new node before
     * @param {object|string|number} dataToInsert The data to initialize with the node
     * @returns {boolean} true if insert operation was successful
     */
    insertBefore: function (nodeData, dataToInsert) {
        var index = this.indexOf(nodeData);
        return this.insertAt(index, dataToInsert);
    },

    /**
     * Inserts a node after the first node containing the provided data
     *
     * @param {object|string|number} nodeData The data of the node to
     *         find to insert the new node after
     * @param {object|string|number} dataToInsert The data to initialize with the node
     * @returns {boolean} true if insert operation was successful
     */
    insertAfter: function (nodeData, dataToInsert) {
        var index = this.indexOf(nodeData);
        var size = this.getSize();

        // check if we want to insert new node after the tail node
        if (index + 1 === size) {

            // if so, call insert, which will append to the end by default
            return this.insert(dataToInsert);

        } else {

            // otherwise, increment the index and insert there
            return this.insertAt(index + 1, dataToInsert);
        }
    },

    //################## REMOVE methods ####################

    /**
     * Removes the tail node from the list
     *
     * There is a significant performance improvement with the operation
     * over its singly linked list counterpart.  The mere fact of having
     * a reference to the previous node improves this operation from O(n)
     * (in the case of singly linked list) to O(1).
     *
     * @returns the node that was removed
     */
    remove: function() {
        if (this.isEmpty()) {
            return null;
        }

        // get handle for the tail node
        var nodeToRemove = this.getTailNode();

        // if there is only one node in the list, set head and tail
        // properties to null
        if (this.getSize() === 1) {
            this.head = null;
            this.tail = null;

        // more than one node in the list
        } else {
            this.tail = this.getTailNode().prev;
            this.tail.next = null;
        }
        this.size -= 1;

        return nodeToRemove;
    },

    /**
     * Removes the head node from the list
     *
     * @returns the node that was removed
     */
    removeFirst: function() {
        if (this.isEmpty()) {
            return null;
        }

        var nodeToRemove;

        if (this.getSize() === 1) {
            nodeToRemove = this.remove();
        } else {
            nodeToRemove = this.getHeadNode();
            this.head = this.head.next;
            this.head.prev = null;
            this.size -= 1;
        }

        return nodeToRemove;
    },

    /**
     * Removes the node at the index provided
     *
     * @param {number} index The index of the node to remove
     * @returns the node that was removed
     */
    removeAt: function (index) {
        var nodeToRemove = this.findAt(index);

        // check for index out-of-bounds
        if (index < 0 || index > this.getSize() - 1) {
            return null;
        }

        // if index is 0, we just need to remove the first node
        if (index === 0) {
            return this.removeFirst();
        }

        // if index is size-1, we just need to remove the last node,
        // which remove() does by default
        if (index === this.getSize() - 1) {
            return this.remove();
        }

        nodeToRemove.prev.next = nodeToRemove.next;
        nodeToRemove.next.prev = nodeToRemove.prev;
        nodeToRemove.next = nodeToRemove.prev = null;

        this.size -= 1;

        return nodeToRemove;
    },

    /**
     * Removes the first node that contains the data provided
     *
     * @param {object|string|number} nodeData The data of the node to remove
     * @returns the node that was removed
     */
    removeNode: function (nodeData) {
        var index = this.indexOf(nodeData);
        return this.removeAt(index);
    },

    //################## FIND methods ####################

    /**
     * Returns the index of the first node containing the provided data.  If
     * a node cannot be found containing the provided data, -1 is returned.
     *
     * @param {object|string|number} nodeData The data of the node to find
     * @returns the index of the node if found, -1 otherwise
     */
    indexOf: function(nodeData) {
        this.iterator.reset();
        var current;

        var index = 0;

        // iterate over the list (keeping track of the index value) until
        // we find the node containg the nodeData we are looking for
        while (this.iterator.hasNext()) {
            current = this.iterator.next();
            if (_.isEqual(current.getData(), nodeData)) {
                return index;
            }
            index += 1;
        }

        // only get here if we didn't find a node containing the nodeData
        return -1;
    },

    /**
     * Returns the fist node containing the provided data.  If a node
     * cannot be found containing the provided data, -1 is returned.
     *
     * @param {object|string|number} nodeData The data of the node to find
     * @returns the node if found, -1 otherwise
     */
    find: function(nodeData) {
        // start at the head of the list
        this.iterator.reset();
        var current;

        // iterate over the list until we find the node containing the data
        // we are looking for
        while (this.iterator.hasNext()) {
            current = this.iterator.next();
            if (_.isEqual(current.getData(), nodeData)) {
                return current;
            }
        }

        // only get here if we didn't find a node containing the nodeData
        return -1;
    },

    /**
     * Returns the node at the location provided by index
     *
     * @param {number} index The index of the node to return
     * @returns the node located at the index provided.
     */
    findAt: function(index) {
        // if idx is out of bounds or fn called on empty list, return -1
        if (this.isEmpty() || index > this.getSize() - 1) {
            return -1;
        }

        // else, loop through the list and return the node in the
        // position provided by idx.  Assume zero-based positions.
        var node = this.getHeadNode();
        var position = 0;

        while (position < index) {
            node = node.next;
            position += 1;
        }

        return node;
    },

    /**
     * Determines whether or not the list contains the provided nodeData
     *
     * @param {object|string|number} nodeData The data to check if the list
     *        contains
     * @returns the true if the list contains nodeData, false otherwise
     */
    contains: function (nodeData) {
         if (this.indexOf(nodeData) > -1) {
             return true;
         } else {
             return false;
         }
     }
};



/**
 * Creates a new queue instance and initializes the underlying data
 * structure
 *
 * @constructor
 */
var PriorityQueue = function() {
    this._list = new DoublyLinkedList();
};

/* Functions attached to the PriorityQueue prototype.  All queue instances
 * will share these methods, meaning there will NOT be copies made for each
 * instance.  This will be a huge memory savings since there may be several
 * different queue instances.
 */
PriorityQueue.prototype = {

    /**
     * Determines if the queue is empty
     *
     * @returns {boolean} true if the queue is empty, false otherwise
     */
    isEmpty: function() {
        return this._list.isEmpty();
    },

    /**
     * Returns the size, or number of items in the queue
     *
     * @returns {number} the number of items in the queue
     */
    size: function() {
        return this._list.getSize();
    },

    /**
     * Clears the queue of all data
     */
    clear: function () {
        return this._list.clear();
    },

    /**
     * Adds a new item containing 'data' just before the node with a lower
     * priority.
     *
     * An item is considered to be be a 'higher' priority if
     * the priority is a smaller value than the one that follows.  For
     * example, an item with priority '1' is considered higher priority than
     * an item with priority '2'--the lower the number, the higher the
     * priority.
     *
     * If pri is not provided, the priority will default to null.
     *
     * @param {object} data the data to add to the back of the queue
     * @param {number} pri the priority of the item.  The lower the number
     *                 the higher the priority. Defaults to null if not
     *                 provided
     */
    enqueue: function (data, pri) {

        // build the payload obj to add to the underlying
        // data structure
        var payload = {
            data: data,
            priority: pri || null
        };

        // if the queue is empty, just add the payload
        if (this.isEmpty() || payload.priority === null) {
            return this._list.insert(payload);
        }

        var current = this._list.getHeadNode();

        // iterate over the queue to find an item with a lower priority,
        // then assign that to the current item
        while (current !== null &&
               current.getData().priority <= payload.priority &&
               current.getData().priority !== null) {
            current = current.next;
        }

        // if we get the back of the queue without finding a lower priority
        // item, just append the payload to the back of the queue
        if (current === null) {
            return this._list.insert(payload);
        }

        // if we get here, we have landed somewhere in the middle of the
        // queue, so insert the payload before the current item, which
        // has a lower priority
        return this._list.insertBefore(current.getData(), payload);

    },

    /**
     * Removes the item from the front of the queue
     *
     * @returns {object} the item, or data, from the front of the queue
     */
    dequeue: function () {
        return this._list.removeFirst().getData();
    },

    /**
     * Returns the data of the item at the front of the queue,
     * but does not remove it
     *
     * @returns {object} the item, or data, from the front of the queue
     */
    peek: function () {
        return this._list.getHeadNode().getData();
    }

};

Object.defineProperty(Object.prototype, "data", { writable : false, configurable : false });

var queue = new PriorityQueue();

if (queue.isEmpty() !== true) { throw("Oopsie!") };

queue.enqueue('some test data', 1);
queue.enqueue('some more test data', 1);
queue.enqueue('and yet some more...', 1);

if (queue.size() !== 3) { throw("Oopsie boo!") };
