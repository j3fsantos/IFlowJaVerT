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
// ------------------------------- dictionary.js -----------------------------

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
    dictionary.containsKey = function (key) {
        return !buckets.isUndefined(dictionary.get(key));
    };

    /**
     * Removes all keys and values from the dictionary.
     * @this {buckets.Dictionary}
     */
    dictionary.clear = function () {
        table = {};
        nElements = 0;
    };

    /**
     * Returns the number of key-value pais in the dictionary.
     * @return {number} The number of key-value mappings in the dictionary.
     */
    dictionary.size = function () {
        return nElements;
    };

    /**
     * Returns true if the dictionary contains no keys.
     * @return {boolean} True if this dictionary contains no mappings.
     */
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
        other.forEach(function (k, v) {
            isEqual = eqf(dictionary.get(k), v);
            return isEqual;
        });
        return isEqual;
    };

    return dictionary;
};


// ---------------------------------- set.js ---------------------------------

/**
 * Creates an empty set.
 * @class <p>A set is a data structure that contains no duplicate items.</p>
 * <p>If the inserted elements are custom objects, a function
 * that converts elements to unique strings must be provided at construction time. 
 * <p>Example:</p>
 * <pre>
 * function petToString(pet) {
 *  return pet.type + ' ' + pet.name;
 * }
 * </pre>
 *
 * @param {function(Object):string=} toStringFunction Optional function used
 * to convert elements to unique strings. If the elements aren't strings or if toString()
 * is not appropriate, a custom function which receives an object and returns a
 * unique string must be provided.
 */
buckets.Set = function (toStringFunction) {

    /** 
     * @exports theSet as buckets.Set
     * @private
     */
    var theSet = {},
        // Underlying storage.
        dictionary = new buckets.Dictionary(toStringFunction);

    /**
     * Returns true if the set contains the specified element.
     * @param {Object} element Element to search for.
     * @return {boolean} True if the set contains the specified element,
     * false otherwise.
     */
    theSet.contains = function (element) {
        return dictionary.containsKey(element);
    };

    /**
     * Adds the specified element to the set if it's not already present.
     * @param {Object} element The element to insert.
     * @return {boolean} True if the set did not already contain the specified element.
     */
    theSet.add = function (element) {
        if (theSet.contains(element) || buckets.isUndefined(element)) {
            return false;
        }
        dictionary.set(element, element);
        return true;
    };

    /**
     * Performs an intersection between this and another set.
     * Removes all values that are not present in this set and the given set.
     * @param {buckets.Set} otherSet Other set.
     */
    theSet.intersection = function (otherSet) {
        theSet.forEach(function (element) {
            if (!otherSet.contains(element)) {
                theSet.remove(element);
            }
        });
    };

    /**
     * Performs a union between this and another set.
     * Adds all values from the given set to this set.
     * @param {buckets.Set} otherSet Other set.
     */
    theSet.union = function (otherSet) {
        otherSet.forEach(function (element) {
            theSet.add(element);
        });
    };

    /**
     * Performs a difference between this and another set.
     * Removes all the values that are present in the given set from this set.
     * @param {buckets.Set} otherSet other set.
     */
    theSet.difference = function (otherSet) {
        otherSet.forEach(function (element) {
            theSet.remove(element);
        });
    };

    /**
     * Checks whether the given set contains all the elements of this set.
     * @param {buckets.Set} otherSet Other set.
     * @return {boolean} True if this set is a subset of the given set.
     */
    theSet.isSubsetOf = function (otherSet) {
        var isSub = true;

        if (theSet.size() > otherSet.size()) {
            return false;
        }

        theSet.forEach(function (element) {
            if (!otherSet.contains(element)) {
                isSub = false;
                return false;
            }
        });
        return isSub;
    };

    /**
     * Removes the specified element from the set.
     * @return {boolean} True if the set contained the specified element, false
     * otherwise.
     */
    theSet.remove = function (element) {
        if (!theSet.contains(element)) {
            return false;
        }
        dictionary.remove(element);
        return true;
    };

    /**
     * Executes the provided function once per element
     * present in the set.
     * @param {function(Object):*} callback Function to execute, it's
     * invoked an element as argument. To break the iteration you can
     * optionally return false inside the callback.
     */
    theSet.forEach = function (callback) {
        dictionary.forEach(function (k, v) {
            return callback(v);
        });
    };

    /**
     * Returns an array containing all the elements in the set in no particular order.
     * @return {Array} An array containing all the elements in the set.
     */
    theSet.toArray = function () {
        return dictionary.values();
    };

    /**
     * Returns true if the set contains no elements.
     * @return {boolean} True if the set contains no elements.
     */
    theSet.isEmpty = function () {
        return dictionary.isEmpty();
    };

    /**
     * Returns the number of elements in the set.
     * @return {number} The number of elements in the set.
     */
    theSet.size = function () {
        return dictionary.size();
    };

    /**
     * Removes all the elements from the set.
     */
    theSet.clear = function () {
        dictionary.clear();
    };

    /**
     * Returns true if the set is equal to another set.
     * Two sets are equal if they have the same elements.
     * @param {buckets.Set} other The other set.
     * @return {boolean} True if the set is equal to the given set.
     */
    theSet.equals = function (other) {
        var isEqual;
        if (buckets.isUndefined(other) || typeof other.isSubsetOf !== 'function') {
            return false;
        }
        if (theSet.size() !== other.size()) {
            return false;
        }

        isEqual = true;
        other.forEach(function (element) {
            isEqual = theSet.contains(element);
            return isEqual;
        });
        return isEqual;
    };

    return theSet;
};

// -------------------------------- tests -------------------------------------

var set1 = new buckets.Set();
var set2 = new buckets.Set();

var s1 = symb_string(s1);
var s2 = symb_string(s2);

Assume (not (s1 = s2));

set1.add(s1);
set1.add(s2);

set2.add(s2);

// console.log("s1 union s2:");
// s1.union(s2);
// s1.forEach(console.log)

set1.intersection(set2);
var size = set1.size();
var res = set1.toArray()[0];
Assert((size = 1) and (res = s2));

// console.log("s1 \\ s2:");
// s1.difference(s2);
// s1.forEach(console.log)
// 
// console.log("s2 \\ s1:");
// s2.difference(s1);
// s2.forEach(console.log)
