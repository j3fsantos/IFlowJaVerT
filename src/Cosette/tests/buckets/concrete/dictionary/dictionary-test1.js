// -------------------------------- base.js ----------------------------------

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

// ------------------------------- arrays.js ---------------------------------

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


// ----------------------------- dictionary.js -------------------------------

/**
 * Creates an empty dictionary.
 * @class <p>Dictionaries map keys to values, each key can map to at most one value.
 * This implementation accepts any kind of objects as keys.</p>
 *
 * <p>If the keys are custom objects, a function that converts keys to unique
 * strings must be provided at construction time.</p>
 * <p>Example:</p>
 * <pre>
 * function petToString(pet) {
 *  return pet.name;
 * }
 * </pre>
 * @constructor
 * @param {function(Object):string=} toStrFunction Optional function used
 * to convert keys to unique strings. If the keys aren't strings or if toString()
 * is not appropriate, a custom function which receives a key and returns a
 * unique string must be provided.
 */
buckets.Dictionary = function (toStrFunction) {

    /** 
     * @exports dictionary as buckets.Dictionary
     * @private
     */
    var dictionary = {},
        // Object holding the key-value pairs.
        table = {},
        // Number of keys in the dictionary.
        nElements = 0,
        // Function to convert keys unique to strings.
        toStr = toStrFunction || buckets.defaultToString,
        // Special string to prefix keys and avoid name collisions with existing properties.
        keyPrefix = '/$ ';

    /**
     * Returns the value associated with the specified key in the dictionary.
     * @param {Object} key The key.
     * @return {*} The mapped value or
     * undefined if the dictionary contains no mapping for the provided key.
     */
    /* @id dictionary_get */
    dictionary.get = function (key) {
        var pair = table[keyPrefix + toStr(key)];
        if (buckets.isUndefined(pair)) {
            return undefined;
        }
        return pair.value;
    };

    /**
     * Associates the specified value with the specified key in the dictionary.
     * If the dictionary previously contained a mapping for the key, the old
     * value is replaced by the specified value.
     * @param {Object} key The key.
     * @param {Object} value Value to be mapped with the specified key.
     * @return {*} Previous value associated with the provided key, or undefined if
     * there was no mapping for the key or the key/value is undefined.
     */
    /* @id dictionary_set */
    dictionary.set = function (key, value) {
        var ret, k, previousElement;
        if (buckets.isUndefined(key) || buckets.isUndefined(value)) {
            return undefined;
        }

        k = keyPrefix + toStr(key);
        previousElement = table[k];
        if (buckets.isUndefined(previousElement)) {
            nElements += 1;
            ret = undefined;
        } else {
            ret = previousElement.value;
        }
        table[k] = {
            key: key,
            value: value
        };
        return ret;
    };

    /**
     * Removes the value associated with the specified key from the dictionary if it exists.
     * @param {Object} key The key.
     * @return {*} Removed value associated with the specified key, or undefined if
     * there was no mapping for the key.
     */
    /* @id dictionary_remove */
    dictionary.remove = function (key) {
        var k = keyPrefix + toStr(key),
            previousElement = table[k];
        if (!buckets.isUndefined(previousElement)) {
            delete table[k];
            nElements -= 1;
            return previousElement.value;
        }
        return undefined;
    };

    /**
     * Returns an array containing all the keys in the dictionary.
     * @return {Array} An array containing all the keys in the dictionary.
     */
    /* @id dictionary_keys */
    dictionary.keys = function () {
        var array = [],
            name;
        for (name in table) {
            if (Object.prototype.hasOwnProperty.call(table, name)) {
                array.push(table[name].key);
            }
        }
        return array;
    };

    /**
     * Returns an array containing all the values in the dictionary.
     * @return {Array} An array containing all the values in the dictionary.
     */
    /* @id dictionary_values */
    dictionary.values = function () {
        var array = [],
            name;
        for (name in table) {
            if (Object.prototype.hasOwnProperty.call(table, name)) {
                array.push(table[name].value);
            }
        }
        return array;
    };

    /**
     * Executes the provided function once per key-value pair
     * present in the dictionary.
     * @param {function(Object,Object):*} callback Function to execute. Receives
     * 2 arguments: key and value. To break the iteration you can
     * optionally return false inside the callback.
     */
    /* @id dictionary_forEach */
    dictionary.forEach = function (callback) {
        var name, pair, ret;
        for (name in table) {
            if (Object.prototype.hasOwnProperty.call(table, name)) {
                pair = table[name];
                ret = callback(pair.key, pair.value);
                if (ret === false) {
                    return;
                }
            }
        }
    };

    /**
     * Returns true if the dictionary contains a mapping for the specified key.
     * @param {Object} key The key.
     * @return {boolean} True if the dictionary contains a mapping for the
     * specified key.
     */
    /* @id dictionary_containsKey */
    dictionary.containsKey = function (key) {
        return !buckets.isUndefined(dictionary.get(key));
    };

    /**
     * Removes all keys and values from the dictionary.
     * @this {buckets.Dictionary}
     */
    /* @id dictionary_clear */
    dictionary.clear = function () {
        table = {};
        nElements = 0;
    };

    /**
     * Returns the number of key-value pais in the dictionary.
     * @return {number} The number of key-value mappings in the dictionary.
     */
    /* @id dictionary_size */
    dictionary.size = function () {
        return nElements;
    };

    /**
     * Returns true if the dictionary contains no keys.
     * @return {boolean} True if this dictionary contains no mappings.
     */
    /* @id dictionary.isEmpty */
    dictionary.isEmpty = function () {
        return nElements <= 0;
    };

    /**
     * Returns true if the dictionary is equal to another dictionary.
     * Two dictionaries are equal if they have the same key-value pairs.
     * @param {buckets.Dictionary} other The other dictionary.
     * @param {function(Object,Object):boolean=} equalsFunction Optional
     * function to check if two values are equal. If the values in the dictionaries
     * are custom objects you should provide a custom equals function, otherwise
     * the === operator is used to check equality between values.
     * @return {boolean} True if the dictionary is equal to the given dictionary.
     */
    /* @id dictionary_equals */
    dictionary.equals = function (other, equalsFunction) {
        var eqf, isEqual;
        if (buckets.isUndefined(other) || typeof other.keys !== 'function') {
            return false;
        }
        if (dictionary.size() !== other.size()) {
            return false;
        }
        eqf = equalsFunction || buckets.defaultEquals;
        isEqual = true;
        /* @id dictionary_equals_callback */
        other.forEach(function (k, v) {
            isEqual = eqf(dictionary.get(k), v);
            return isEqual;
        });
        return isEqual;
    };

    return dictionary;
};

// --------------------------------- tests -----------------------------------

var elems = 100,
    dict;

var beforeEach = function () {
    dict = new buckets.Dictionary();
};

// test 1
//it('set and get value with string key', function () {
beforeEach();
var i;
dict.get('sd');

// test with string keys
for (i = 0; i < elems; i += 1) {
    dict.set('' + i, i + 1);
}
dict.size();

for (i = 0; i < elems; i += 1) {
    dict.get('' + i);
}

dict.set('a', 5);
dict.get('a');
dict.set('a', 21);
dict.size();
dict.get('a');


