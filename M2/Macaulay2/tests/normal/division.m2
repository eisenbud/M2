R = ZZ[t..u, Degrees => {2:1}, MonomialOrder => { MonomialSize => 32, GroupRevLex => 2, Position => Up}, Inverses => true]
assert( (quotientRemainder(1-t^3,1-t)) === (1+t+t^2,0_R) )
assert( (quotientRemainder(1-t^3,1-t)) === (1+t+t^2,0_R) )
assert( (quotientRemainder(1-t^3,1-t)) === (1+t+t^2,0_R) )
assert( (quotientRemainder(1-t^3,1-t)) === (1+t+t^2,0_R) )
assert( (quotientRemainder(1-u^3,1-u)) === (0_R,1-u^3) )
assert( (quotientRemainder(1-u^3,1-u)) === (0_R,1-u^3) )
assert( (quotientRemainder(1-u^3,1-u)) === (0_R,1-u^3) )
assert( (quotientRemainder(1-u^3,1-u)) === (0_R,1-u^3) )
assert( (quotientRemainder(1-u^3,1-u)) === (0_R,1-u^3) )
R = ZZ[t..u, Degrees => {2:1}, MonomialOrder => { MonomialSize => 32, Weights => {0,-1}, GroupRevLex => 2, Position => Up}, Inverses => true]
assert( (quotientRemainder(1-t^3,1-t)) === (0_R,1-t^3) )
assert( (quotientRemainder(1-t^3,1-t)) === (0_R,1-t^3) )
assert( (quotientRemainder(1-t^3,1-t)) === (0_R,1-t^3) )
assert( (quotientRemainder(1-t^3,1-t)) === (0_R,1-t^3) )
assert( (quotientRemainder(1-u^3,1-u)) === (1+u+u^2,0_R) )
assert( (quotientRemainder(1-u^3,1-u)) === (1+u+u^2,0_R) )
assert( (quotientRemainder(1-u^3,1-u)) === (1+u+u^2,0_R) )
assert( (quotientRemainder(1-u^3,1-u)) === (1+u+u^2,0_R) )
assert( (quotientRemainder(1-u^3,1-u)) === (1+u+u^2,0_R) )
end
generateAssertions ///
R = ZZ[t..u, Degrees => {2:1}, MonomialOrder => { MonomialSize => 32, GroupRevLex => 2, Position => Up}, Inverses => true]
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
R = ZZ[t..u, Degrees => {2:1}, MonomialOrder => { MonomialSize => 32, Weights => {0,-1}, GroupRevLex => 2, Position => Up}, Inverses => true]
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-t^3,1-t)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
quotientRemainder(1-u^3,1-u)
///
