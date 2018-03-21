function insert(node, value) {
    
    var result;

    if (node === null) {
        result = { next: null, value: value }
    } else if (node.value < value) {
        var rec = insert(node.next, value);
        result = { next: rec, value: node.value }
    } else {
      result = { next: node, value: node.value } //BUG: [node.value] instead of [value]
//      result = { next: node, value: value } //correct one
    }

    return result;
}

function append(list, value) {
  return { next: list, value: value };
}

function sort(head) {
    var result;

    if (head === null) {

        result = null
    } else {
        var rec = sort(head.next);
        result = insert(rec, head.value)
    }
    return result;
}

var n1 = symb_number(n1);
var n2 = symb_number(n2);
var n3 = symb_number(n3);

Assume((not (n1 = n2)) and (not (n2 = n3)) and (not (n3 = n1)));

var l = null;
l = append(l, n1);
l = append(l, n2);
l = append(l, n3);

var sorted = sort(l);
var r1 = sorted.value;
var r2 = sorted.next.value;
var r3 = sorted.next.next.value;
Assert((r1 < r2) and (r2 < r3));