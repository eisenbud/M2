Hom(Module, Module, ZZ) := Matrix => (M,N,d) -> (
    --M,N homogeneous
    
    --efficiently compute Hom up to degree d
    --check that the hypotheses are satisfied:
    S := ring M;    
    m := presentation M;
    n := presentation N;    
    m1 = map(M,coker m, 1);
    n1 = map(N,coker n, 1);

    if not 
       ( --degreeLength S == 1 and 
	isHomogeneous m and 
	isHomogeneous n) then 
	error"expected graded modules";
    M0:= target m;
    m' := transpose m;
    M0' := source m';
    M1' := target m';
    N0 := target n;

    h := syz(m'**N0 | M1'**n, 
             SyzygyRows => rank N0*rank M0', 
	     DegreeLimit => d);
    p := positions(degrees source h, e -> e <= {d});
--    hp := h_p;
   maps0 = apply(p, pp-> map(N, M, matrix reshape(N0, M0, h_{pp})));
   select(maps0, a -> a!=0)
	)


--need to create "homomorphism"
end --
(f) -> map(N,M,adjoint'(f,M,N), Degree => first degrees source f);

restart
load "HomWithLimit.m2"
needsPackage "Truncations" 
TEST /// -*getting the degree shift right*-
   S = ZZ/32003[x_1..x_3]
   m = random(S^3, S^{4:-2})
   A = random(target m, target m)
   B = random(source m, source m)
   m' = A*m*B
   H1 = Hom(coker m, coker m')
   gens H1
--   Hom(coker m, coker m') % truncate(2,Hom(coker m, coker m'))
   h2= Hom (coker m, coker m',2)
   
   h2_0*(h2_1//h2_0) == h2_1
   (h2_1//h2_0)
prune Hom(coker m, coker m')

   S = ZZ/32003[x_1..x_3]
   m = random(S^{0,1}, S^{4:-2})
   A = random(target m, target m)
   B = random(source m, source m)
   m' = A*m*B
   M = coker m
   M' = coker m'
   H1 = Hom(coker m, coker m')
   H2 = truncate(2,H1)
   h0=Hom (coker m, coker m',0)
   h1=   Hom (coker m, coker m',1)
   h2=   Hom (coker m, coker m',2)      
degrees h0
degrees h1
degrees source h2
degrees presentation H1
degrees H1
mingens image h2
map(M',M,h2_{1})

prune Hom(coker m, coker m')
///

-*
restart
load "HomWithLimit.m2"

*-

TEST///--getting the degrees right in matrixHom
debug needsPackage "Isomorphism"
S = ZZ/101[x,y]
m = matrix{{x,y}}
n = matrix{{x^2, y^2}}

setRandomSeed 0
assert(all(flatten for a from -2 to 2 list for b from -2 to 2 list(
a = -2;b=2;
(v, diffdegs) = checkDegrees (S^{a}**(m++m),S^{b}**(m++m));
((prune coker randomMinimalDegreeHomomorphism(S^{a}**(m++m),S^{b}**(m++m),-diffdegs_0) == 0))
), t -> t))
///



TEST///
S= ZZ/101[a,b]
A = S^1++S^{-1}
B = S^{3}
Hom(A,B,-5)
///

TEST///-*"isIsomorphic"*-
needsPackage "Points"
canonicalIdeal = method()
canonicalIdeal Ideal := Ideal => I ->(
    S := ring I;
    R := S/I;
    F := res I;
    omega := coker sub(transpose F.dd_(length F), R);
    H := Hom(omega,R^1);
    deg := max degrees source gens H;
    g := (gens H)*random(source gens H, R^-deg);
    trim sub(ideal g,R) ---canonical ideal of a 1-dim ring.
)

kk=ZZ/32003
S = kk[x,y,z]

d = 15
I = points randomPointsMat(S,d);
elapsedTime W = canonicalIdeal I;
R = ring W;
n =1
M = module(trim W^n)
N = Hom(M, R^1)
Hom(M,N, -4)
g = (isIsomorphic (N,M))_1;
assert (isWellDefined g)
assert(source g == M)
assert(target g == N)
assert(coker g == 0)
assert(ker g == 0)
///

