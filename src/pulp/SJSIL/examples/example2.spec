spec xpto (x, y)
  [[ ((x, "foo") -> "bar") * ((x, "baz") -> y + 1) * (y == _w + 3) ]]
  [[ ((x, "foo") -> none) * ((x, "baz") -> _w) ]]
  normal;
  
  [[ ((x, "foo") -> "googoo") * ((x, "baz") -> y + 1) * (y == _w + 3) ]]
  [[ ((x, "foo") -> none) * ((x, "gaga") -> _w) ]]
  normal
