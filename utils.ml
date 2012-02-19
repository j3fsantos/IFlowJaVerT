open List

let flat_map f l = flatten (map f l)

let flip f x y = f y x

exception LessThanOne
exception EmptyList

let rec take n ys = 
  match (n,ys) with
    | (1, (x::xs)) -> x
    | (_, (x::xs)) -> if (n>0) then take (n-1) xs else raise LessThanOne
    | (_, []) -> raise EmptyList

let rec drop n ys = 
  match (n,ys) with
    | (1, (x::xs)) -> xs
    | (_, (x::xs)) -> if (n>0) then drop (n-1) xs else raise LessThanOne
    | (_, []) -> raise EmptyList

let rec takeWhile p ys = 
  match ys with
    | [] -> []
    | (x::xs) -> if (p x) then x::(takeWhile p xs) else []

let rec dropWhile p ys = 
  match ys with
    | [] -> []
    | (x::xs) -> if (p x) then dropWhile p xs else xs
