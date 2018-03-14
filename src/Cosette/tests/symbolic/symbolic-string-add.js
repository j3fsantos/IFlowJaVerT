var v1 = jsil_make_symbolic_string();

var v2 = jsil_make_symbolic_string();

var vs = { a: v1, b: v2 };
vs.a + "_" + vs.b + "-" + vs.a + "_" + vs.b;

//var vs = [ v1, v2 ];
//vs[0] + "_" + vs[1] + "-" + vs[0] + "_" + vs[1];
