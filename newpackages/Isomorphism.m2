-*
We could use surjective map in both directions for the iso checks 

*-

newPackage(
    "Isomorphism",
    Version => "0.5",
    Date => "April 12, 2022",
    Headline => "Probabalistic tests of isomorphism",
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
    "Strict" -- option making the homogeneous case preserve degrees.
    }
    

-* Code section *-

isDegreeListZero = L -> 
-- test whether a list of lists has all entries of entries 0
   all(L, s -> 
           all(s,  e-> e === 0)); 

checkDegrees = method(Options =>{Verbose =>false})
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
		return "inhomogeneous");
	    
	dA := sort degrees Abar;
        dB := sort degrees Bbar;
	
        degdiffs := for i from 0 to #dA-1 list dA_i-dB_i;
        matches := all(degdiffs, s-> s == degdiffs_0);
        if matches then(
        	--now the degrees of the generators are euqal.
        if v and not isDegreeListZero degdiffs then 
	       <<"To make the degree sequences equal, tensor "<<A<<"with ring " << A << "to " << {dA_0-dB_0} <<endl;
               return (true, dA_0-dB_0)
	               );
	        --now matches == false
  	if v then <<"degree sequences don't match"<<endl;
	(false, null)
    )

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
    S := ring A;
    H := Hom(A,B);
    Hp := prune H;
    pmap := Hp.cache.pruningMap;
    if o.Homogeneous then (
	d := min degrees Hp;
	f := homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^{-d})))
	    ) else
              f = homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^1)));
    	t := if o.Homogeneous and prune coker f == 0 or coker f == 0 then true else false;
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
        if o.Homogeneous == true and 
	        not (isHomogeneous A and isHomogeneous B) then 
	        error"inputs not homogeneous";
    	S := ring A;
	<<"pruning two modules in isIso"<<endl;
elapsedTime	A1 := prune A;
        a1 := A1.cache.pruningMap; --iso from A1 to A
elapsedTime	B1 := prune B;
        b1 := B1.cache.pruningMap; --iso from B1 to B
	--handle the cases where one of A,B is 0
	isZA1 := A1==0;
	isZB1 := B1==0;	
    	if isZA1 =!= isZB1 then return (false, null );
	if isZA1 and isZB1 then return (true, map(A,B,0));

	-- from now on, A1 and B1 are nonzero
	<<"entering checkDegrees"<<endl;
elapsedTime	df := checkDegrees (A1,B1,Verbose => o.Verbose);
	if o.Strict and o.Homogeneous and not isDegreeListZero (df_1) then
	     return(false, null);
	if class df_1 =!= List then return (false, null);
	--now there is a chance at an isomorphism up to shift, 
	--and df is the degree diff.
	<<"computing Hom"<<endl;
elapsedTime        H := Hom(A1,B1);       
	kk := ultimate(coefficientRing, S);
	if o.Homogeneous === true then
	      sH := select(H_*, f-> degree f == -df_1) else 
	      sH = H_*;
	if #sH == 0 then return false;
	<<"random sum of maps"<<endl;
elapsedTime	g := sum(sH, f-> random(kk)*homomorphism matrix f);
	kmodule := coker vars S;
	gbar := kmodule ** g;
	if gbar==0  then return false;
	
	t1 := elapsedTime (prune coker gbar) == 0 ;
	if t1 == false then return (false, null);
	
	t2 := elapsedTime prune ker g == 0;
	if t2 then (true, g) else (false, null)
	)
isIso = isIsomorphic
-*
restart
loadPackage("Isomorphism", Reload =>true)
*-
///
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
assert((isIsomorphic(C1,C2, Homogeneous => false))_0 ==true)
assert((isIsomorphic(A1,A2))_0 == true)
assert(coker ((isIsomorphic(A1,A2))_1) == 0)
assert((isIsomorphic (A,A))_0 == true)
assert((isIsomorphic(B1,B1))_0 == true)
assert((isIsomorphic(A,B1))_0 == false)
assert(isIsomorphic(A1,B1, Verbose => true) == false)
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
 [checkDegrees, Verbose]
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
   isIsomorphic (S^{{-3,-3}}**A,A) -- problem.
   
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

   --isIsomorphic(C1,C2) -- gives an error because C2 is not homogeneous
   assert((isIsomorphic(C1,C2, Homogeneous => false))_0 ==true)
   assert((isIsomorphic(A1,A2))_0 == true)
   assert(coker ((isIsomorphic(A1,A2))_1) == 0)
   assert((isIsomorphic (A,A))_0 == true)
   assert((isIsomorphic(B1,B1))_0 == true)
   assert((isIsomorphic(A,B1))_0 == false)
   assert((isIsomorphic(A1,B1, Verbose => true))_0==false)
///

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
M = module(trim W^n)
N=Y;
alpha = presentation M;
--beta = presentation N;
p = map(N,target beta,1)
--this is the place to restrict the degrees: there are 15 of degree -12, 420 of degree -11, and we want the degree -12.
elapsedTime ker ((transpose alpha)**p);
-*
Basic setup:
F->G ->M
P->Q ->N
the homomorphisms G->Q that induce maps M ->N are the first factor part of
ker(Hom(G,Q) ++ Hom(F,P) -> Hom(F,Q).)
--want the matrices that have a specific degree.
*-
X' = prune module trim (W^n)
Y = prune Hom(X, R^1)

M = X';

           Y := youngest(M.cache.cache,N.cache.cache);
           if Y#?(Hom,M,N) then return Y#(Hom,M,N);
elapsedTime phi = (transpose presentation M ** N);
elapsedTime K = ker phi;
elapsedTime trim K;
betti K

elapsedTime H1 = intersect(image (alpha**target beta), image(target alpha**beta));



           H := trim kernel (transpose presentation M ** N);
           H.cache.homomorphism = (f) -> map(N,M,adjoint'(f,M,N), Degree => first degrees source f);
           Y#(Hom,M,N) = H; -- a hack: we really want to type "Hom(M,N) = ..."
           H.cache.formation = FunctionApplication { Hom, (M,N) };
           H)

prune X
checkDegrees(X,Y, Verbose =>true)
H = Hom(X,Y);
elapsedTime H' = Hom(X',Y);


print d;
for n from 2 to 20 do (
    print n;
elapsedTime X = module(trim W^n);
elapsedTime Y = prune Hom(X, R^1);
elapsedTime ans = (isIsomorphic(X, Y))_0;
<< ans<<endl;
<<endl);
)
///
end--

-* Development section *-
restart
needsPackage "Isomorphism"
check "Isomorphism"

restart
uninstallPackage "Isomorphism"
restart
installPackage "Isomorphism"
viewHelp "Isomorphism"
    
restart
