var o = [1, 10];
var p1_string = symb_string(p1);
var v1_string = symb_string(v1);
o[ p1_string ] = v1_string;

function f1(ary) {
    var sum = 0;
    for (var i in ary) {
        sum = sum + ary[i];
    }
    return sum;
}

var res = typeof(f1(o));
console.log(res);
//Assert(res = "string");
