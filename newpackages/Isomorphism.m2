newPackage(
    "Isomorphism",
    Version => "0.7",
    Date => "April 12, 2022",
    Headline => "Probabalistic test of isomorphism",
    Authors => {{Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"}
                  },
    DebuggingMode => true
    )

export {
    "isIsomorphic",
    "surjectiveMap",
    "checkDegrees",
    --
    "Strict" -- option for checkDegrees making the homogeneous case preserve degrees.
    }
    

-* Code section *-

randomMinimalDegreeHomomorphism=method()
randomMinimalDegreeHomomorphism(Matrix, Matrix, ZZ) := Matrix => (m,n,d) -> (
    --m,n homogeneous, minimal over a ring with degree length 1 (this restridd
    
    --given free presentations
    --M = coker m:M1 -> M0 
    --N = coker n: N1 -> N0
    --(ring M)^diffdegs has the same degrees as N,
    --so if diffdegs  is positive, then 
    -- M is generated in higher degrees than N, and
    --the iso M->N has degree -diffdegs
    
    --efficiently compute 
    --the matrices of a random degree homomorphisms M -> N of degree  -diffdegs.
    
    --check that the hypotheses are satisfied:
    S := ring m;    
    resField := S^1/(ideal gens S);
    if not 
       (degreeLength S == 1 and 
	isHomogeneous m and 
	isHomogeneous n and
	m**resField == 0 and
	n**resField == 0) then 
	error"Unsuitable ring, modules or presentations.";
	
    M0:= target m;
    m' := transpose m;
    M0' := source m';
    M1' := target m';
    N0 := target n;

    h := syz(m'**N0 | M1'**n, 
             SyzygyRows => rank N0*rank M0', 
	     DegreeLimit => -{d});
	 
    p := positions(degrees source h, e -> e == -{d});
    hp := h_p;
    a := hp*random(source (hp), S^{d}); --represents general map of degree -diffdegs
    map(coker n, coker m, matrix reshape(N0, M0, a))
    )

isDegreeListZero = L -> 
-- test whether a list of lists has all entries of entries 0
   all(L, s -> 
           all(s,  e-> e === 0)); 

checkDegrees = method(Options =>{Verbose =>false, Strict =>false})
checkDegrees(Module, Module) := Sequence => o -> (A,B) -> (
    v := o.Verbose;
    S := ring A;
    mm := ideal gens S;
    Abar := A/(mm*A);
    Bbar := B/(mm*B);
    if numgens Abar != numgens Bbar then (
		if v then <<"numbers of generators are different"<<endl;
	        return (false, null)
	        );
    if not (isHomogeneous A and isHomogeneous B) then (
                if v then <<"numbers of generators agree"<<endl;
		return (true,{"inhomogeneous"}));
	    
	dA := sort degrees Abar;
        dB := sort degrees Bbar;
	if o.Strict == true and not dA == dB then return(false, );
	
        degdiffs := for i from 0 to #dA-1 list dA_i-dB_i;
        matches := all(degdiffs, s-> s == degdiffs_0);
        if matches then(
        	--now the degrees of the generators are euqal.
        if v and not isDegreeListZero degdiffs then 
	       <<"To make the degree sequences equal, tensor "<<A<<"with ring " << A << "to " << {dA_0-dB_0} <<endl;
               return (true, dA_0-dB_0)
	               );
--	error();
	        --now matches == false
  	if v then <<"degree sequences don't match"<<endl;
	(false, null)
    )
checkDegrees(Matrix, Matrix) := Sequence => o-> (m,n) -> checkDegrees(target m, target n, o)

///
restart
loadPackage "Isomorphism"
S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
A = S^{{2,1}}
B1 = S^{{1,1}}
B = S^{{1,1}, {2,3}}
d = checkDegrees(A,B, Verbose => true)
assert(d == (false,null))
d = checkDegrees(A,B1)
checkDegrees(B,B)
e = checkDegrees(S^{d_1}**A, B1)
assert (e_0 == true)
///

surjectiveMap = method(Options => {Homogeneous => true})
surjectiveMap(Module, Module) := Sequence => o -> (A,B)->(
    mm := ideal gens ring A;
    if isHomogeneous A and isHomogeneous B then (
	    Abar := A/(mm*A);
    	    Bbar := B/(mm*B);
	    if min degrees generators Bbar < min degrees gens Abar then
	    	return (false, )
		);
    S := ring A;
    H := Hom(A,B); -- this may be sloooow.
    Hp := prune H;
    pmap := Hp.cache.pruningMap;
    if o.Homogeneous then (
	d := min degrees Hp;
	f := homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^{-d})))
	    ) else
        f = homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^1)));
    	t := if o.Homogeneous and prune coker f == 0 or coker f == 0 then 
	      true else false;
    (t,f))
///
restart
errorDepth = 0
debug loadPackage "Isomorphism"
S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
B1 = S^{{1,1}}
B = S^{{1,1}, {2,3}}
A = coker random(B, S^{2:-{2,2}})
B = A
checkDegrees(A,B)
d = checkDegrees(A,B1)
checkDegrees(B,B)
checkDegrees(S^{d}**A, B1)
///

isIsomorphic = method(Options =>{Homogeneous => true, Verbose => false, Strict =>false})
isIsomorphic(Module, Module) := sequence => o ->  (A,B)->(
    --returns a pair (false, null) or (true, f), or where f is an isomorphism 
    --f: A to B.
    --if an inhomogeneous iso is to be allowed, use the option
    --Homogeneous => false
        v := o.Verbose;
	
        if o.Homogeneous == true and 
	        not (isHomogeneous A and isHomogeneous B) then 
	        error"inputs not homogeneous";
    	S := ring A;
	resS := S/(ideal gens S);

    	m := presentation A;
	if m**resS == 0 then A1 := A else 
	        (m = presentation (A1 = prune A);
	        a1 := A1.cache.pruningMap);
    	n := presentation B;
	if n**resS == 0 then B1 := B else
	        (n = presentation (B1 = prune B);
	        b1 := B1.cache.pruningMap); --iso from B1 to B

	--handle the cases where one of A,B is 0
	isZA1 := target m ==0;
	isZB1 := target n ==0;	
    	if isZA1 =!= isZB1 then return (false, null );
	if isZA1 and isZB1 then return (true, map(A,B,0));

	-- from now on, A1 and B1 are nonzero

	df := checkDegrees (A1,B1,Verbose => o.Verbose, Strict => o.Strict);
--	if o.Strict and o.Homogeneous and not isDegreeListZero df_1 then
--	     return(false, null);
	if class df_1 =!= List  then return (false, null);
	--now there is a chance at an isomorphism up to shift, 
	--and df is the degree diff.

	--compute an appropriate random map g
	if o.Homogeneous and degreeLength S == 1 then
	g := randomMinimalDegreeHomomorphism(m,n, df_1_0) else (
        H := Hom(A1,B1);       
	kk := ultimate(coefficientRing, S);
	if o.Homogeneous === true then
	      sH := select(H_*, f-> degree f == -df_1) else 
	      sH = H_*;
	if #sH == 0 then return false;
    	g = sum(sH, f-> random(kk)*homomorphism matrix f)
	);
        
	--test g to see if it's surjective:
	kmodule := coker vars S;
	gbar := kmodule ** g;
	
	t1 := prune coker gbar == 0;
	if t1 == false then return (false, null);
	
	t2 := prune ker g == 0;
	if t2 then (true, g) else (false, null)
	)


-*
restart
loadPackage("Isomorphism", Reload =>true)
*-
///
setRandomSeed 0
S = ZZ/32003[a,b,Degrees => {{1,0},{0,1}}]
B1 = S^{{1,1}}
B = S^{{1,1}, {2,3}}
A = coker random(B, S^{2:-{3,3}})
A1 = coker (a = random(B1^3, S^{2:-{3,3}}))
A2 = coker (random(target a, target a)*a*random(source a,source a))
C1 = coker (a = random(B1^3, S^{2:-{3,3}, -{4,5}}))
C2 = coker (matrix random(S^3, S^3)*matrix a*matrix random(S^3,S^3))

--isIsomorphic(C1,C2) -- gives an error because C2 is not homogeneous
assert((isIsomorphic(C1,C2, Homogeneous => false))_0 ==true)
isIsomorphic(C1,C2, Homogeneous => false) -- this should be true!

isIsomorphic(C1,C1, Homogeneous => false) -- this should be true!


assert((isIsomorphic(A1,A2))_0 == true)
assert(coker ((isIsomorphic(A1,A2))_1) == 0)
assert((isIsomorphic (A,A))_0 == true)
assert((isIsomorphic(B1,B1))_0 == true)
assert((isIsomorphic(A,B1))_0 == false)
assert((isIsomorphic(A1,B1, Verbose => true))_0 === false)
///


-* Documentation section *-
beginDocumentation()

doc ///
Key
 Isomorphism
Headline
 Probabalistic test for isomorphism
Description
  Text
   Two modules are isomorphic if there is a surjection in each direction.
   These routines produce random combinations of the generators of Hom
   and test whether these are surjections.
SeeAlso
 checkDegrees
 surjectiveMap
///

doc ///
Key
 checkDegrees
 (checkDegrees,Module,Module)
 (checkDegrees,Matrix,Matrix)
 [checkDegrees, Verbose]
 [checkDegrees, Strict] 
Headline
 compares the degrees of generators of two modules
Usage
 d = checkDegrees(A,B)
Inputs
 A:Module
 B:Module
Outputs
 d:List
  a degree in the ring of A and B
Description
  Text
   This is to be used with @TO isIsomorphic@.
   
   The routine compares the sorted lists of degrees of generators of the two modules;
   the degreeLength (can be anything).
   If the numbers of generators of A,B are different, the modules are not isomorphic
   If the numbers are the same, and all the corresponding degrees pairs differ
   by the same amount (so that the modules might become isomorphic after a shift, 
   the output tells how to adjust the modules to make the degrees equal.
  Example
   S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
   A = S^{{2,1}}
   B = S^{{1,1}}
   C = S^{{1,1}, {2,3}}
   d = (checkDegrees(A,B))_1
   checkDegrees(S^{d}**A, B)
   checkDegrees(A,C)
   checkDegrees(B,B)
SeeAlso
 isIsomorphic
///


doc ///
Key
 isIsomorphic
 (isIsomorphic, Module, Module)
 [isIsomorphic, Verbose]
 [isIsomorphic, Homogeneous]
 [isIsomorphic, Strict] 
Headline
 Probabalistic test for isomorphism of modules
Usage
 t = isIsomorphic (A,B)
Inputs
 A:Module
 B:Module
 Homogeneous => Boolean
Outputs
 t:Boolean
Description
  Text
   In case both modules are homogeneous the program first uses @TO checkDegrees@
   to see whether an isomorphism is possible. This may be an isomorphism up to shift
   if Strict => false (the default) or on the nose if Strict => true.
   
   If this test is passed, the program uses a variant of the Hom command
   to compute a random map of minimal possible degree from A to B,
   and checks whether this is surjective and injective.
   
   In the inhomogeneous case (or with Homogeneous => false) the random map is
   a random linear combination of a basis of generators of the module of homomorphisms.
   
  Example
   setRandomSeed 0
   S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
   B1 = S^{{1,1}}
   B = S^{{1,1}, {2,3}}
   A = coker random(B, S^{2:-{3,3}})
   A1 = coker (a = random(B1^3, S^{2:-{3,3}}))
   A2 = coker (random(target a, target a)*a*random(source a,source a))
   C1 = coker (a = random(B1^3, S^{2:-{3,3}, -{4,5}}))
   C2 = coker (matrix random(S^3, S^3)*matrix a*matrix random(S^3,S^3))

   --isIsomorphic(C1,C2) -- gives an error because C2 is not homogeneous
   isIsomorphic (S^{{-3,-3}}**A,A)
   isIsomorphic (S^{{-3,-3}}**A,A, Strict=>true)
   isIsomorphic(C1,C2, Homogeneous => false)
   isIsomorphic(A1,A2)
   coker((isIsomorphic(A1,A2))_1) == 0

   isIsomorphic(B1,B1)
   isIsomorphic(A,B1)
   isIsomorphic(A1,B1, Verbose => true) 

   S = ZZ/32003[x_1..x_3]
   m = random(S^3, S^{4:-2})
   A = random(target m, target m)
   B = random(source m, source m)
   m' = A*m*B
   isIsomorphic (coker m, coker m')
   isIsomorphic (S^{-3}**coker m, coker m')
   isIsomorphic (S^{-3}**coker m, coker m', Strict => true)
Caveat
 If isHomogeneous => true (the default) then
 To be isomorphic with this test the two modules 
 have to be homogeneous and generated in degrees 
 all with the same offset
SeeAlso
 checkDegrees
///
-* Test section *-
-*
restart
loadPackage "Isomorphism"
*-

TEST /// -*getting the degree shift right*-
   S = ZZ/32003[x_1..x_3]
   m = random(S^3, S^{4:-2})
   A = random(target m, target m)
   B = random(source m, source m)
   m' = A*m*B
   checkDegrees (S^{-3}**coker m, coker m')
///

-*
restart
uninstallPackage "Isomorphism"
restart
installPackage "Isomorphism"
*-

TEST///--getting the degrees right in matrixHom
debug needsPackage "Isomorphism"
S = ZZ/101[x,y]
m = matrix{{x,y}}
n = matrix{{x^2, y^2}}

setRandomSeed 0
assert(all(flatten for a from -2 to 2 list for b from -2 to 2 list(
(v, diffdegs) = checkDegrees (S^{a}**(m++m),S^{b}**(m++m));
((prune coker randomMinimalDegreeHomomorphism(S^{a}**(m++m),S^{b}**(m++m),diffdegs_0) == 0))
), t -> t))
///


TEST /// -* various cases of isomorphism *-
   setRandomSeed 0
   S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
   B1 = S^{{1,1}}
   B = S^{{1,1}, {2,3}}
   A = coker random(B, S^{2:-{3,3}})
   A1 = coker (a = random(B1^3, S^{2:-{3,3}}))
   A2 = coker (random(target a, target a)*a*random(source a,source a))
   C1 = coker (a = random(B1^3, S^{2:-{3,3}, -{4,5}}))
   C2 = coker (matrix random(S^3, S^3)*matrix a*matrix random(S^3,S^3))

   assert((isIsomorphic(C1,C2, Homogeneous => false))_0 ==true)
   assert((isIsomorphic(A1,A2))_0 == true)
   assert(coker ((isIsomorphic(A1,A2))_1) == 0)
   assert((isIsomorphic (A,A))_0 == true)
   assert((isIsomorphic(B1,S^{{1,1}}**B1))_0 == true)   
   assert((isIsomorphic(B1,S^{{1,1}}**B1, Strict=>true))_0 == false)
   assert((isIsomorphic(A,B1))_0 == false)
   assert((isIsomorphic(A1,B1, Verbose => true))_0==false)
///

-*
here!
restart
debug loadPackage "Isomorphism"
*-
TEST///
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
n =2
M = prune module(trim W^n)
elapsedTime N = prune Hom(M, R^1)
elapsedTime (g = (isIsomorphic (M,N))_1)
assert (isWellDefined g)
assert(source g == M)
assert(target g == N)
assert(coker g == 0)
assert(ker g == 0)

///
end--

-* Development section *-
restart
uninstallPackage "Isomorphism"
restart
installPackage "Isomorphism"
check "Isomorphism"
viewHelp "Isomorphism"
    
restart


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
n =2
M = prune module(trim W^n)
elapsedTime N = prune Hom(M, R^1)

for n from 2 to 20 do (
    print n;
X = module(trim W^n);
Y = prune Hom(X, R^1);
elapsedTime ans = (isIsomorphic(X, Y))_0;
<< ans<<endl;
<<endl);
