// --------------------------------- _base.js --------------------------------

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

// ------------------------------- arrays.js ----------------------------------

/**
 * @namespace Contains various functions for manipulating arrays.
 */
buckets.arrays = {};

/**
 * Returns the index of the first occurrence of the specified item
 * within the specified array.
 * @param {*} array The array.
 * @param {*} item The element to search for.
 * @param {function(Object,Object):boolean=} equalsFunction Optional function to
 * check equality between two elements. Receives two arguments and returns true if they are equal.
 * @return {number} The index of the first occurrence of the specified element
 * or -1 if not found.
 */
buckets.arrays.indexOf = function (array, item, equalsFunction) {
    var equals = equalsFunction || buckets.defaultEquals,
        length = array.length,
        i;
    for (i = 0; i < length; i += 1) {
        if (equals(array[i], item)) {
            return i;
        }
    }
    return -1;
};

/**
 * Returns the index of the last occurrence of the specified element
 * within the specified array.
 * @param {*} array The array.
 * @param {Object} item The element to search for.
 * @param {function(Object,Object):boolean=} equalsFunction Optional function to
 * check equality between two elements. Receives two arguments and returns true if they are equal.
 * @return {number} The index of the last occurrence of the specified element
 * within the specified array or -1 if not found.
 */
buckets.arrays.lastIndexOf = function (array, item, equalsFunction) {
    var equals = equalsFunction || buckets.defaultEquals,
        length = array.length,
        i;
    for (i = length - 1; i >= 0; i -= 1) {
        if (equals(array[i], item)) {
            return i;
        }
    }
    return -1;
};

/**
 * Returns true if the array contains the specified element.
 * @param {*} array The array.
 * @param {Object} item The element to search for.
 * @param {function(Object,Object):boolean=} equalsFunction Optional function to
 * check equality between two elements. Receives two arguments and returns true if they are equal.
 * @return {boolean} True if the specified array contains the specified element.
 */
buckets.arrays.contains = function (array, item, equalsFunction) {
    return buckets.arrays.indexOf(array, item, equalsFunction) >= 0;
};

/**
 * Removes the first ocurrence of the specified element from the specified array.
 * @param {*} array The array.
 * @param {*} item The element to remove.
 * @param {function(Object,Object):boolean=} equalsFunction Optional function to
 * check equality between two elements. Receives two arguments and returns true if they are equal.
 * @return {boolean} True If the array changed after this call.
 */
buckets.arrays.remove = function (array, item, equalsFunction) {
    var index = buckets.arrays.indexOf(array, item, equalsFunction);
    if (index < 0) {
        return false;
    }
    array.splice(index, 1);
    return true;
};

/**
 * Returns the number of elements in the array equal
 * to the specified element.
 * @param {Array} array The array.
 * @param {Object} item The element.
 * @param {function(Object,Object):boolean=} equalsFunction Optional function to
 * check equality between two elements. Receives two arguments and returns true if they are equal.
 * @return {number} The number of elements in the specified array.
 * equal to the specified item.
 */
buckets.arrays.frequency = function (array, item, equalsFunction) {
    var equals = equalsFunction || buckets.defaultEquals,
        length = array.length,
        freq = 0,
        i;
    for (i = 0; i < length; i += 1) {
        if (equals(array[i], item)) {
            freq += 1;
        }
    }
    return freq;
};

/**
 * Returns true if the provided arrays are equal.
 * Two arrays are considered equal if both contain the same number
 * of elements and all corresponding pairs of elements
 * are equal and are in the same order.
 * @param {Array} array1
 * @param {Array} array2
 * @param {function(Object,Object):boolean=} equalsFunction Optional function to
 * check equality between two elements. Receives two arguments and returns true if they are equal.
 * @return {boolean} True if the two arrays are equal.
 */
buckets.arrays.equals = function (array1, array2, equalsFunction) {
    var equals = equalsFunction || buckets.defaultEquals,
        length = array1.length,
        i;

    if (array1.length !== array2.length) {
        return false;
    }
    for (i = 0; i < length; i += 1) {
        if (!equals(array1[i], array2[i])) {
            return false;
        }
    }
    return true;
};

/**
 * Returns a shallow copy of the specified array.
 * @param {*} array The array to copy.
 * @return {Array} A copy of the specified array.
 */
buckets.arrays.copy = function (array) {
    return array.concat();
};

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

/**
 * Executes the provided function once per element present in the array.
 * @param {Array} array The array.
 * @param {function(Object):*} callback Function to execute,
 * invoked with an element as argument. To break the iteration you can
 * optionally return false in the callback.
 */
buckets.arrays.forEach = function (array, callback) {
    var lenght = array.length,
        i;
    for (i = 0; i < lenght; i += 1) {
        if (callback(array[i]) === false) {
            return;
        }
    }
};

// ------------------------------ our test now -------------------------------

var x1 = symb_number(x1);
var x2 = symb_number(x2);
var x3 = symb_number(x3);

var array = [ x1, x2 ];

var nbElem = 0;
buckets.arrays.forEach(array, function(x) { nbElem++ });

var lastIndex = buckets.arrays.lastIndexOf(array, x1);

Assume((not (x3 = x1)) and (not (x1 = x2)));
var notFoundIndex = buckets.arrays.indexOf(x3);

// asserts
Assert(nbElem = 2);
Assert(((x1 = x2) and (lastIndex = 1)) or ((not (x1 = x2)) and (lastIndex = 0)));
Assert(notFoundIndex = -1);

