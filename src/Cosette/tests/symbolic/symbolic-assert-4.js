var o = [1, 10];
o[ p1_string ] = v1_string;

function f1(ary) {
    var sum = 0;
    for (var i in ary) {
        sum = sum + ary[i];
    }
    return sum;
}

f1(o);
