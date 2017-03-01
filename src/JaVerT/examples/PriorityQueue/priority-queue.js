/**
 * @fileOverview Implementation of a priority queue data structure
 * @author Jason S. Jones
 * @license MIT
 */

(function() {
    'use strict';

    // bring in the one dependency which will be the underlying
    // data structure for this queue implementation
    var LinkedList = require('dbly-linked-list');

    /**
     * Creates a new queue instance and initializes the underlying data
     * structure
     *
     * @constructor
     */
    var PriorityQueue = function() {
        this._list = new LinkedList();
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

    module.exports = PriorityQueue;
}());