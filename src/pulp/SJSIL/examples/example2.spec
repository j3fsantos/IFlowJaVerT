spec xpto (x, y)
  pre: ((x, "foo") -> "bar") * ((x, "baz") -> y + 1) * (y == _w + 3),
  post: ((x, "foo") -> none) * ((x, "baz") -> _w),
  flag: normal
