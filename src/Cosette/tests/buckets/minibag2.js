// --------------------------------- _base.js --------------------------------

'use strict';

/**
 * Top level namespace for Buckets,
 * a JavaScript data structure library.
 * @name buckets
 */
var buckets = {};


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

    return dictionary;
};

// ---------------------------------- bag.js ---------------------------------

/**
 * Creates an empty bag.
 * @class <p>A bag is a special kind of set in which members are
 * allowed to appear more than once.</p>
 * <p>If the inserted elements are custom objects, a function
 * that maps elements to unique strings must be provided at construction time.</p>
 * <p>Example:</p>
 * <pre>
 * function petToUniqueString(pet) {
 *  return pet.type + ' ' + pet.name;
 * }
 * </pre>
 *
 * @constructor
 * @param {function(Object):string=} toStrFunction Optional function
 * to convert elements to unique strings. If the elements aren't strings or if toString()
 * is not appropriate, a custom function which receives an object and returns a
 * unique string must be provided.
 */
buckets.Bag = function (toStrFunction) {

    /** 
     * @exports bag as buckets.Bag
     * @private
     */
    var bag = {},
        // Function to convert elements to unique strings.
        toStrF = toStrFunction || buckets.defaultToString,
        // Underlying  Storage
        dictionary = new buckets.Dictionary(toStrF),
        // Number of elements in the bag, including duplicates.
        nElements = 0;
    /**
     * Adds nCopies of the specified element to the bag.
     * @param {Object} element Element to add.
     * @param {number=} nCopies The number of copies to add, if this argument is
     * undefined 1 copy is added.
     * @return {boolean} True unless element is undefined.
     */
    bag.add = function (element, nCopies) {
        var node;
        if (isNaN(nCopies) || buckets.isUndefined(nCopies)) {
            nCopies = 1;
        }
        if (buckets.isUndefined(element) || nCopies <= 0) {
            return false;
        }

        if (!bag.contains(element)) {
            node = {
                value: element,
                copies: nCopies
            };
            dictionary.set(element, node);
        } else {
            dictionary.get(element).copies += nCopies;
        }
        nElements += nCopies;
        return true;
    };

    /**
     * Counts the number of copies of the specified element in the bag.
     * @param {Object} element The element to search for.
     * @return {number} The number of copies of the element, 0 if not found.
     */
    bag.count = function (element) {
        if (!bag.contains(element)) {
            return 0;
        }
        return dictionary.get(element).copies;
    };

    /**
     * Returns true if the bag contains the specified element.
     * @param {Object} element Element to search for.
     * @return {boolean} True if the bag contains the specified element,
     * false otherwise.
     */
    bag.contains = function (element) {
        return dictionary.containsKey(element);
    };

    /**
     * Removes nCopies of the specified element from the bag.
     * If the number of copies to remove is greater than the actual number
     * of copies in the bag, all copies are removed.
     * @param {Object} element Element to remove.
     * @param {number=} nCopies The number of copies to remove, if this argument is
     * undefined 1 copy is removed.
     * @return {boolean} True if at least 1 copy was removed.
     */
    bag.remove = function (element, nCopies) {
        var node;
        if (isNaN(nCopies) || buckets.isUndefined(nCopies)) {
            nCopies = 1;
        }
        if (buckets.isUndefined(element) || nCopies <= 0) {
            return false;
        }

        if (!bag.contains(element)) {
            return false;
        }
        node = dictionary.get(element);
        if (nCopies > node.copies) {
            nElements -= node.copies;
        } else {
            nElements -= nCopies;
        }
        node.copies -= nCopies;
        if (node.copies <= 0) {
            dictionary.remove(element);
        }
        return true;
    };

    /**
     * Returns the number of elements in the bag, including duplicates.
     * @return {number} The number of elements in the bag.
     */
    bag.size = function () {
        return nElements;
    };

    return bag;
};

// ------------------------------ our tests now ------------------------------


// Check that the size is ok when removing duplicated (or not) elements;
var s1 = symb_string(s1);
var s2 = symb_string(s2);
var s3 = symb_string(s3);
Assume ((not (s1 = s2)) and (not (s1 = s3)));

var bag = new buckets.Bag();

bag.add(s1);
bag.add(s2);
bag.add(s3);
bag.remove(s2);
bag.remove(s2); // if s2 = s3, we remove both, otherwise s3 is still in there
var res = bag.size();
Assert (((s2 = s3) and (res = 1)) or ((not (s2 = s3)) and (res = 2)));