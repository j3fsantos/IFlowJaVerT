'use strict';

/**
 * Top level namespace for Buckets,
 * a JavaScript data structure library.
 * @id buckets
 */
var buckets = {};

/**
 * Default function to compare element order.
 * @function
 * @private
 */
/* @id base_defaultCompare */
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
/* @id base_defaultEquals */
buckets.defaultEquals = function (a, b) {
    return a === b;
};

/**
 * Default function to convert an object to a string.
 * @function
 * @private
 */
/* @id base_defaultToString */
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
/* @id base_isFunction */
buckets.isFunction = function (func) {
    return (typeof func) === 'function';
};

/**
 * Checks if the given argument is undefined.
 * @function
 * @private
 */
/* @id base_isUndefined */
buckets.isUndefined = function (obj) {
    return obj === undefined;
};

/**
 * Checks if the given argument is a string.
 * @function
 * @private
 */
/* @id base_isString */
buckets.isString = function (obj) {
    return Object.prototype.toString.call(obj) === '[object String]';
};

/**
 * Reverses a compare function.
 * @function
 * @private
 */
/* @id base_reverseCompareFunction */
buckets.reverseCompareFunction = function (compareFunction) {
    if (!buckets.isFunction(compareFunction)) {
        /* @id base_reverseCompareFunction_inner1 */
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
    /* @id base_reverseCompareFunction_inner2 */
    return function (d, v) {
        return compareFunction(d, v) * -1;
    };

};

/**
 * Returns an equal function given a compare function.
 * @function
 * @private
 */
/* @id base_compareToEquals */
buckets.compareToEquals = function (compareFunction) {
    return function (a, b) {
        return compareFunction(a, b) === 0;
    };
};


// ---------------------------- linkedlist.js --------------------------------

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
    /* @id list_nodeAtIndex */
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
    /* @id list_add */
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
    /* @id list_first */
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
    /* @id list_last */
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
    /* @id list_elementAtIndex */
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
    /* @id list_indexOf */
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
    /* @id list_contains */
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
    /* @id list_remove */
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
    /* @id list_clear */
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
    /* @id list_equals */
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
        /* @id list_equals_callback */
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
    /* @id list_removeElementAtIndex */
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
    /* @id list_forEach */
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
    /* @id list_reverse */
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
    /* @id list_toArray */
    list.toArray = function () {
        var result = [];
        /* @id list_toArray_callback */
        list.forEach(function (element) {
            result.push(element);
        });
        return result;
    };

    /**
     * Returns the number of elements in the list.
     * @return {number} The number of elements in the list.
     */
    /* @id list_size */
    list.size = function () {
        return nElements;
    };

    /**
     * Returns true if the list contains no elements.
     * @return {boolean} true if the list contains no elements.
     */
    /* @id list_isEmpty */
    list.isEmpty = function () {
        return nElements <= 0;
    };

    return list;
};

// ---------------------------------- tests ----------------------------------

var elems = 5,
    list;

function equals(a, b) {
    return a.el === b.el;
}

var beforeEach = function() {
    list = new buckets.LinkedList();
};

//it('add inserts elements in proper sequence', function () {
beforeEach();
var i;
list.first();
list.last();
list.size();
for (i = 0; i < elems; i += 1) {
    list.add(i);
list.first();
list.last();

    if (i === 0) {
list.first();
    }
list.size();
}


//it('reverse gives the right ordering with >2 elements', function () {
beforeEach();
list.add(1);
list.add(2);
list.add(3);
list.reverse();
list.elementAtIndex(0);
list.elementAtIndex(1);
list.elementAtIndex(2);


//it('reverse gives the right ordering with 2 elements', function () {
beforeEach();
list.add(1);
list.add(2);
list.reverse();
list.elementAtIndex(0);
list.elementAtIndex(1);


//it('reverse gives the right ordering with 1 element', function () {
beforeEach();
list.add(1);
list.reverse();
list.elementAtIndex(0);
list.elementAtIndex(1);


//it('clear removes all elements', function () {
beforeEach();
var i;
for (i = 0; i < elems; i += 1) {
    list.add(i);
}
list.clear();
list.first();
list.last();
list.size();

//it('size gives the right value', function () {
beforeEach();
list.size();
list.add(1);
list.size();
list.add(1);
list.size();


//it('elementAtIndex returns the correct value', function () {
beforeEach();
var i, J;
list.elementAtIndex(-1);
list.elementAtIndex(0);
list.elementAtIndex(1);

for (i = 0; i < elems; i += 1) {
    list.add(i);
list.elementAtIndex(list.size() - 1);
list.elementAtIndex(i);

    for (j = 0; j < i; j += 1) {
list.elementAtIndex(j);
    }
}


//it('equals returns true only if lists have the elements in the same order', function () {
beforeEach();
var list2 = new buckets.LinkedList();
list.add(1);
list.add(2);


list2.add(1);
list2.add(2);

list.equals(list2);
list2.clear();
list2.add(2);
list2.add(1);
list.equals(list2);
list.equals([1, 2]);


//it("add doesn't insert element into invalid index", function () {
beforeEach();
list.add(0, 1);
list.size() === 0;
list.first();
list.last();


//it('add inserts elements to the last index', function () {
beforeEach();
var i;
for (i = 0; i < elems; i += 1) {
list.add(i, i);
list.elementAtIndex(i);
list.first();
list.last();
    if (i === 0) {
list.first();
    }
list.size();
}

//it('add inserts elements to the first index', function () {
beforeEach();
var i, j;
for (j = 0; j < elems; j += 1) {
    for (i = 0; i < j; i += 1) {
        list.add(i);
    }
    list.add(-i, 0);
list.elementAtIndex(0);
list.first();
}

//it('add inserts elements to custom index', function () {
beforeEach();
var j;
for (j = 0; j < elems; j += 1) {
    list.add(j);
}

list.add(-100, elems / 2);
list.elementAtIndex(elems / 2);



//it('indexOf finds inserted elements', function () {
beforeEach();
var j;
list.indexOf(0);
for (j = 0; j < elems; j += 1) {
    list.add(j + 1);
list.indexOf(j + 1);
list.indexOf(-100);
}
for (j = 0; j < elems; j += 1) {
list.indexOf(j + 1);
list.indexOf(-100);
}


//it('indexOf finds elements with custom equals function', function () {
beforeEach();
var j;
list.indexOf({
    el: 1
}, equals);
for (j = 0; j < elems; j += 1) {
    list.add({
        el: j + 1
    });
list.indexOf({
        el: j + 1
    }, equals);
list.indexOf({
        el: -200
    }, equals);
}
for (j = 0; j < elems; j += 1) {
list.indexOf({
        el: j + 1
    }, equals);
list.indexOf({
        el: -200
    }, equals);
}

//it('remove deletes inserted elements', function () {
beforeEach();
var i, half;
list.remove(1);
list.size() === 0;
list.last();
list.first();

for (i = 0; i < elems; i += 1) {
    list.add(i);
list.remove(i);
list.size() === 0;
list.last();
list.first();
}

list.add(1);
list.add(2);
list.remove(1);
list.size() === 1;
list.first();
list.last();
list.clear();

list.add(1);
list.add(2);
list.add(3);
list.add(4);
list.remove(2);
list.size() === 3;
list.first();
list.last();
list.elementAtIndex(0);
list.elementAtIndex(1);
list.elementAtIndex(2);
list.elementAtIndex(3);
list.clear();

for (i = 0; i < elems; i += 1) {
    list.add(i);
}
half = elems / 2;
list.remove(elems / 2);
for (i = 0; i < elems; i += 1) {
    if (i === (half)) {
list.indexOf(i);
    } else if (i < half) {
list.indexOf(i);
    } else if (i > half) {
list.indexOf(i);
    }
}
list.size() === (elems - 1);

//it("remove returns false for non-existing elements", function () {
beforeEach();
list.remove(5);
list.size();
list.add(1);
list.add(2);
list.add(3);
list.add(4);
list.remove(5);
list.size();

//it('remove deletes elements with custom equals', function () {
beforeEach();
var i;
list.remove({
    el: 1
});
for (i = 0; i < elems; i += 1) {
    list.add({
        el: i
    });
}
for (i = 0; i < elems; i += 1) {
list.remove({
        el: i
    });
list.remove({
        el: i
    }, equals);
}


//it('removeElementAtIndex deletes elements at specified index', function () {
beforeEach();
list.removeElementAtIndex(0);
list.removeElementAtIndex(-1);
list.removeElementAtIndex(1);
list.size() === 0;

list.add(1);

list.removeElementAtIndex(-1);
list.removeElementAtIndex(1);
list.size() === 1;

list.removeElementAtIndex(0);
list.size() === 0;
list.first();
list.last();
list.elementAtIndex(0);

list.add(1);
list.add(2);
list.removeElementAtIndex(0);
list.size() === 1;
list.first();

list.clear();
list.add(1);
list.add(2);
list.add(3);
list.removeElementAtIndex(2);
list.size() === 2;
list.first();
list.last();
list.clear();

list.add(1);
list.add(2);
list.add(3);
list.add(4);
list.add(5);

list.removeElementAtIndex(2);
list.size() === 4;
list.first();
list.last();

list.elementAtIndex(0);
list.elementAtIndex(1);
list.elementAtIndex(2);
list.elementAtIndex(3);

//it('toArray returns elements in proper order', function () {
beforeEach();
var arr;
list.toArray().length;

list.add(5);
arr = list.toArray();
arr[0];
arr.length;

list.add(8);
arr = list.toArray();
arr[0];
arr[1];
arr.length;


//it('forEeach gives all the elements in the right order', function () {
beforeEach();
var i;
list.forEach(function (e) {
true; // should not enter here
});

for (i = 0; i < elems; i += 1) {
    list.add(i);
}

i = 0;
list.forEach(function (e) {
e;
    i += 1;
});

//it('forEeach can be interrupted', function () {
beforeEach();
var array = [0, 1, 2, 3, 4],
    b = [],
    i;
for (i = 0; i < elems; i += 1) {
    list.add(i);
}
list.forEach(function (e) {
    b.push(e);
    if (e === 4) {
        return false;
    }
});

array;
