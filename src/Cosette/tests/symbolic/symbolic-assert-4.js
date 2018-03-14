var o = [1, 10];
o[ ___p1_string ] = ___v1_string;

function f1(ary) {
    var sum = 0;
    for (var i in ary) {
        sum = sum + ary[i];
    }
    return sum;
}

f1(o);
