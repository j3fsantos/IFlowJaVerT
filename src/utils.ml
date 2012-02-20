open List

let flat_map f l = flatten (map f l)

exception LessThanOne
exception EmptyList
