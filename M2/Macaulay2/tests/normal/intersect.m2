R = ZZ/101[x,y]

assert(intersect ideal (-1)_R === ideal 1_R)
assert(intersect ideal"x2,y"  === ideal"y,x2")
assert(intersect{ideal"x2,y"} === ideal"y,x2")
assert(intersect(ideal"x2,y", ideal"x,y2") === ideal"y2,xy,x2")
assert(intersect{ideal"x2,y", ideal"x,y2"} === ideal"y2,xy,x2")
assert(intersect(ideal"x2,y", ideal"x,y2", ideal"x,y3") === ideal"xy,x2,y3")
assert(intersect{ideal"x2,y", ideal"x,y2", ideal"x,y3"} === ideal"xy,x2,y3")

assert(intersect(monomialIdeal"x2,y", ideal"x,y2") === monomialIdeal"y2,xy,x2")
assert(intersect(ideal"x2,y", monomialIdeal"x,y2") ===         ideal"y2,xy,x2")

assert(
     intersect(image matrix {{1},{x}}, image matrix {{x}, {x^2}})
     == image matrix {{x}, {x^2}}
     )
assert(
     intersect(image matrix {{1},{x}}, image matrix {{x}, {x^3}}) ==  0
     )
assert( intersect( ideal(x^2,y), ideal (x,y^2)) == ideal (y^2, x^2, x*y) )

--
R = ZZ/101[a..d]
assert(
     intersect(
	  subquotient(matrix {{a}},matrix {{d}}),
	  subquotient(matrix {{b}},matrix{{d}})
	  )
     ==
     subquotient(matrix {{a*b}},matrix {{d}})
     )
