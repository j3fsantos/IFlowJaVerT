var total = "";

var o = { };

o[0] = function f_double(x) {
    return x + x;   
};

o[1] = function f_prefix(x) {
    return "p_" + x;
};

o[2] = function f_postfix(x) {
    return x + "_p";
};

o[0]("x");
o[1]("x");
o[2]("x");

var n = ev1_number;
if (n == 0 || n == 1 || n == 2) {
    total = o[ n ]( s_string );
}

total;
