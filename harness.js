var NotEarlyErrorString = "NotEarlyError";
var EarlyErrorRePat = "^((?!" + NotEarlyErrorString + ").)*$";
var NotEarlyError = new Error(NotEarlyErrorString);

function Test262Error(message) {
    this.message = message || "";
}

Test262Error.prototype.toString = function () {
    return "Test262Error: " + this.message;
};

var _ERROR;
_ERROR = function _ERROR(message) {
    throw new Test262Error(message);
};

function testFailed(message) {
    _ERROR(message);
}

function assert(mustBeTrue, message) {
    if (mustBeTrue === true) {
        return;
    }

    if (message === undefined) {
        message = 'Expected true but got ' + String(mustBeTrue);
    }
    _ERROR(message);
}

assert._isSameValue = function (a, b) {
    if (a === b) {
        // Handle +/-0 vs. -/+0
        return a !== 0 || 1 / a === 1 / b;
    }

    // Handle NaN vs. NaN
    return a !== a && b !== b;
};

assert.sameValue = function (actual, expected, message) {
    if (assert._isSameValue(actual, expected)) {
        return;
    }

    if (message === undefined) {
        message = '';
    } else {
        message += ' ';
    }

    message += 'Expected SameValue(«' + String(actual) + '», «' + String(expected) + '») to be true';

    _ERROR(message);
};

assert.notSameValue = function (actual, unexpected, message) {
    if (!assert._isSameValue(actual, unexpected)) {
        return;
    }

    if (message === undefined) {
        message = '';
    } else {
        message += ' ';
    }

    message += 'Expected SameValue(«' + String(actual) + '», «' + String(unexpected) + '») to be false';

    _ERROR(message);
};

assert.throws = function (expectedErrorConstructor, func, message) {
    if (typeof func !== "function") {
        _ERROR('assert.throws requires two arguments: the error constructor ' +
            'and a function to run');
        return;
    }
    if (message === undefined) {
        message = '';
    } else {
        message += ' ';
    }

    try {
        func();
    } catch (thrown) {
        if (typeof thrown !== 'object' || thrown === null) {
            message += 'Thrown value was not an object!';
            _ERROR(message);
        } else if (thrown.constructor !== expectedErrorConstructor) {
            message += 'Expected a ' + expectedErrorConstructor.name + ' but got a ' + thrown.constructor.name;
            _ERROR(message);
        }
        return;
    }

    message += 'Expected a ' + expectedErrorConstructor.name + ' to be thrown but no exception was thrown at all';
    _ERROR(message);
};

function isConfigurable(obj, name) {
    try {
        delete obj[name];
    } catch (e) {
        if (!(e instanceof TypeError)) {
            _ERROR("Expected TypeError, got " + e);
        }
    }
    return !Object.prototype.hasOwnProperty.call(obj, name);
}

function isEnumerable(obj, name) {
    return Object.prototype.hasOwnProperty.call(obj, name) &&
        Object.prototype.propertyIsEnumerable.call(obj, name);
}

function isEqualTo(obj, name, expectedValue) {
    var actualValue = obj[name];

    return assert._isSameValue(actualValue, expectedValue);
}

function isWritable(obj, name, verifyProp, value) {
    var newValue = value || "unlikelyValue";
    var hadValue = Object.prototype.hasOwnProperty.call(obj, name);
    var oldValue = obj[name];
    var writeSucceeded;

    try {
        obj[name] = newValue;
    } catch (e) {
        if (!(e instanceof TypeError)) {
            _ERROR("Expected TypeError, got " + e);
        }
    }

    writeSucceeded = isEqualTo(obj, verifyProp || name, newValue);

    // Revert the change only if it was successful (in other cases, reverting
    // is unnecessary and may trigger exceptions for certain property
    // configurations)
    if (writeSucceeded) {
      if (hadValue) {
        obj[name] = oldValue;
      } else {
        delete obj[name];
      }
    }

    return writeSucceeded;
}

function verifyEqualTo(obj, name, value) {
    if (!isEqualTo(obj, name, value)) {
        _ERROR("Expected obj[" + String(name) + "] to equal " + value +
                   ", actually " + obj[name]);
    }
}

function verifyWritable(obj, name, verifyProp, value) {
    if (!verifyProp) {
        assert(Object.getOwnPropertyDescriptor(obj, name).writable,
               "Expected obj[" + String(name) + "] to have writable:true.");
    }
    if (!isWritable(obj, name, verifyProp, value)) {
        _ERROR("Expected obj[" + String(name) + "] to be writable, but was not.");
    }
}

function verifyNotWritable(obj, name, verifyProp, value) {
    if (!verifyProp) {
        assert(!Object.getOwnPropertyDescriptor(obj, name).writable,
               "Expected obj[" + String(name) + "] to have writable:false.");
    }
    if (isWritable(obj, name, verifyProp)) {
        _ERROR("Expected obj[" + String(name) + "] NOT to be writable, but was.");
    }
}

function verifyEnumerable(obj, name) {
    assert(Object.getOwnPropertyDescriptor(obj, name).enumerable,
           "Expected obj[" + String(name) + "] to have enumerable:true.");
    if (!isEnumerable(obj, name)) {
        _ERROR("Expected obj[" + String(name) + "] to be enumerable, but was not.");
    }
}

function verifyNotEnumerable(obj, name) {
    assert(!Object.getOwnPropertyDescriptor(obj, name).enumerable,
           "Expected obj[" + String(name) + "] to have enumerable:false.");
    if (isEnumerable(obj, name)) {
        _ERROR("Expected obj[" + String(name) + "] NOT to be enumerable, but was.");
    }
}

function verifyConfigurable(obj, name) {
    assert(Object.getOwnPropertyDescriptor(obj, name).configurable,
           "Expected obj[" + String(name) + "] to have configurable:true.");
    if (!isConfigurable(obj, name)) {
        _ERROR("Expected obj[" + String(name) + "] to be configurable, but was not.");
    }
}

function verifyNotConfigurable(obj, name) {
    assert(!Object.getOwnPropertyDescriptor(obj, name).configurable,
           "Expected obj[" + String(name) + "] to have configurable:false.");
    if (isConfigurable(obj, name)) {
        _ERROR("Expected obj[" + String(name) + "] NOT to be configurable, but was.");
    }
}