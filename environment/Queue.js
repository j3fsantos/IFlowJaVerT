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
 * @id  Node
 * @rec false
 *
 * @constructor
 * @param {object|number|string} data The data to initialize with the node
 *
 * @pre  (standardObject(this) * emptyNode(this) * types(data : $$object_type))
 * @post (standardObject(this) * Node(this, data, $$null, $$null))
 */
function Node(data) {
    this.data = data;
    this.prev = null;
    this.next = null;
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
     * @id   n_hasNext
     * @rec  false
     *
     * @pre  (standardObject(this) * dataField(this, "next", $$null))
     * @post (standardObject(this) * dataField(this, "next", $$null) * (ret == $$f))
     *
     * @pre  (standardObject(this) * ((this, "next") -> None))
     * @post (standardObject(this) * ((this, "next") -> None) * (ret == $$t))
     *
     * @pre  (standardObject(this) * dataField(this, "next", #v) * (! (#v == $$null)))
     * @post (standardObject(this) * dataField(this, "next", #v) * (ret == $$t))
     *
     */
    hasNext: function () {
        return (this.next !== null);
    },

    /**
     * Returns whether or not the node has a pointer to the previous node
     *
     * @returns {boolean} true if there is a previous node; false otherwise
     *
     * @id   n_hasPrev
     * @rec  false
     *
     * @pre  (standardObject(this) * dataField(this, "prev", $$null))
     * @post (standardObject(this) * dataField(this, "prev", $$null) * (ret == $$f))
     *
     * @pre  (standardObject(this) * ((this, "prev") -> None))
     * @post (standardObject(this) * ((this, "prev") -> None) * (ret == $$t))
     *
     * @pre  (standardObject(this) * dataField(this, "prev", #v) * (! (#v == $$null)))
     * @post (standardObject(this) * dataField(this, "prev", #v) * (ret == $$t))
     */
    hasPrev: function () {
        return (this.prev !== null);
    },

    /**
     * Returns the data of the the node
     *
     * @returns {object|string|number} the data of the node
     *
     * @id   n_getData
     * @rec  false
     *
     * @pre  (standardObject(this) * ((this, "data") -> None))
     * @post (standardObject(this) * ((this, "data") -> None) * (ret == $$undefined))
     *
     * @pre  (standardObject(this) * dataField(this, "data", #v))
     * @post (standardObject(this) * dataField(this, "data", #v) * (ret == #v))
     */
    getData: function () {
        return this.data;
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
 *
 * @id  DoublyLinkedList
 * @rec false
 *
 */
function DoublyLinkedList() {
    this.head = null;
    this.tail = null;
    this.size = 0;
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
     * @param {object|string|number} data The data to initialize with the node                         
     * @returns {object} Node object intialized with 'data'
     *
     * @id  createNewNode
     * @rec false
     *
     * @pre  (scope(Node : #l_node) * function_object(#l_node, #xsc_Node, "Node", "Node", 1, #pr_node) * NodeProto(#pr_node) *
              types(#l_node : $$object_type, #xsc_Node : $$object_type, #pr_node : $$object_type, data : $$object_type))
     * @post (scope(Node : #l_node) * function_object(#l_node, #xsc_Node, "Node", "Node", 1, #pr_node) * NodeProto(#pr_node) *
              types(#l_node : $$object_type, #xsc_Node : $$object_type, #pr_node : $$object_type, data : $$object_type) * 
              standardObject(ret) * Node(ret, data, $$null, $$null))
     */
    createNewNode: function (data) {
        return new Node(data);
    }
};

/* var queue = new PriorityQueue();

if (queue.isEmpty() !== true) { throw("Oopsie!") };

queue.enqueue('some test data', 1);
queue.enqueue('some more test data', 1);
queue.enqueue('and yet some more...', 1);

if (queue.size() !== 3) { throw("Oopsie boo!") }; */
