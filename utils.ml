open List

let flat_map f l = flatten (map f l)

        
let rec intersperse x ys =
  match ys with
    | [] -> []
    | [y] -> [y]
    | y::ys -> y::x::(intersperse x ys)
