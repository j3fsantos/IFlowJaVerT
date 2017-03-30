/** 
    @pred Node(n, data, prev, next, np) :
        ObjectWithProto(n, np) *
        dataField(n, "data", data) *
        dataField(n, "next", next) *
        dataField(n, "prev", prev) *
        empty_fields (n : "data", "next", "prev" ) * 
        types(data : $$number_type);

    @pred NodePrototype(np) :
        standardObject(np) *
        dataField(np, "hasNext",  #hn_floc) * fun_obj(hasNext,  #hn_floc, #hn_proto) *
        dataField(np, "hasPrev",  #hp_floc) * fun_obj(hasPrev,  #hp_floc, #hp_proto) *
        dataField(np, "getData",  #gd_floc) * fun_obj(getData,  #gd_floc, #gd_proto) *
        dataField(np, "toString", #ts_floc) * fun_obj(toString, #ts_floc, #ts_proto) *
        empty_fields (np : "hasNext", "hasPrev", "getData", "toString" ) ;

*/


(function () {
    'use strict';

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
    @id  Node

    @pre ((data == #data) * types(#data: $$number_type) * ObjectWithProto(this, #np) * 
            NodePrototype(#np) * empty_fields(this : ))

    @post (Node(this, #data, $$null, $$null, #np) * NodePrototype(#np) * (ret == $$empty))
  */
    function Node(data) {
        this.data = data || null;
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
         * 
        @id  hasNext

        @pre  (Node(this, #data, #prev, $$null, #np) * NodePrototype(#np))

        @post (Node(this, #data, #prev, $$null, #np) * NodePrototype(#np) * (ret == $$f))

        @pre  (Node(this, #data, #prev, #next, #np) * NodePrototype(#np) * (! (#next == $$null)))

        @post (Node(this, #data, #prev, #next, #np) * NodePrototype(#np) * (ret == $$t))

         */
        hasNext: function() {
            return (this.next !== null);
        },

        /**         
         * 
        @id  hasPrev
           
        @pre  (Node(this, #data, $$null, #next, #np) * NodePrototype(#np))

        @post (Node(this, #data, $$null, #next, #np) * NodePrototype(#np) * (ret == $$f))

        @pre  (Node(this, #data, #prev, #next, #np) * NodePrototype(#np) * (! (#prev == $$null)))

        @post (Node(this, #data, #prev, #next, #np) * NodePrototype(#np) * (ret == $$t))
         */
        hasPrev: function() {
            return (this.prev !== null);
        },

        /**         
         * 
         @id  getData
         
         @pre  (Node(this, #data, $$null, #next, #np))

         @post (Node(this, #data, $$null, #next, #np) * (ret == #data))   

         */
        getData: function() {
            return this.data;
        },

        /**
         *         
         * @id  toString
         */
        toString: function() {
            if (typeof this.data === 'object') {
                return JSON.stringify(this.data);
            } else {
                return String(this.data);
            }
        }
    };

    module.exports = Node;

}());