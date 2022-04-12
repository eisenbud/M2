-*
The routines should return the isomorphisms they find. the routing surjectiveMap is a good model.
Also, surjective map should be used for the iso checks (needs a homogeneous version).
Also, there should be a routine for equalizing the minimal degree of the generators in the
homogeneous case.
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
    "isHomogeneouslyIsomorphic",
    "isLocallyIsomorphic",
    "surjectiveMap",
    "checkDegrees",
    "correctDegrees"
    }
    

-* Code section *-
checkDegrees = method()
checkDegrees(Module, Module) := (A,B) ->(
    if not isHomogeneous A and isHomogeneous B then error"Input modules not homogeneous";
    degdiff := degrees A - degrees B
    <<"To make the degrees equal"<<endl;
    <<"tensor the first argument with its ring to the power " << degdiff;
    )
///
debug needsPackage "Isomorphism"
S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
A = S^{{2,1}}
B = S^{{1,1}}
checkDegrees(A,B)
checkDegrees(S^d**A, B)
///

surjectiveMap = method()
surjectiveMap(Module,Module) := Boolean => (A,B)->(
    S := ring A;
    H := Hom(A,B);
    Hp := prune H;
    pmap := Hp.cache.pruningMap;
    f := homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^1)));
    t := if prune coker f == 0 then true else false;
    (t,f))
isHomogeneouslyIsomorphic = method()
isHomogeneouslyIsomorphic(Module, Module) := Boolean => (A,B)->(
        if not isHomogeneous A and isHomogeneous B then error"inputs not homogeneous";
    	S := ring A;
	A1 := prune A;
	B1 := prune B;

	--handle the cases where one of A,B is 0
	isZA1 := A1==0;
	isZB1 := B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

	-- from now on, A1 and B1 are nonzero
	dA := degree A1_*_0;
	dB := degree B1_*_0;
	df := dB-dA;
        H := Hom(A1,B1);       
	kk := ultimate(coefficientRing, ring A);
	sH := select(H_*, f-> degree f == df);
	if #sH ==0 then return false;
	g := sum(sH, f-> random(kk)*homomorphism matrix f);
	kmodule := coker vars S;
	gbar := kmodule ** g;
	if gbar==0  then return false;
	(prune coker gbar) == 0 and prune ker g == 0
	)
isIso = isHomogeneouslyIsomorphic

isLocallyIsomorphic = method()
isLocallyIsomorphic(Module,Module) := Boolean =>(A,B)->(
    if isHomogeneous A and isHomogeneous B and
            all(A_*, a->degree a == degree(A_*_0)) and 
	    all(B_*, a->degree a == degree(B_*_0)) then
	return isHomogeneouslyIsomorphic(A,B);

	S := ring A; 
	kk := ultimate(coefficientRing, S);
	kmod := coker vars S;
	A1 := prune A;
	B1 := prune B;

--handle the cases where one of A,B is 0
	isZA1 := A1==0;
	isZB1 := B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

--now we can assume both are nonzero
        H1 := Hom(A1,B1);      
	if #H1_* == 0 then return false;
	g1 := sum(H1_*, f-> random(kk)*(kmod**homomorphism matrix f));
	t1 := (prune coker g1 == 0);
	if t1 == false then return false else(
	    <<"there is a surjection arg1 -> arg2"<<endl;
            H2 := Hom(B1,A1);      
	    if #H2_* == 0 then return false;	    
	    g2 := sum(H2_*, f-> random(kk)*(kmod**homomorphism matrix f));
	    prune coker g2 == 0)
	)
    
-* Documentation section *-
beginDocumentation()

doc ///
Key
  Isomorphism
Headline
 Probabalistic tests for isomorphism
Description
  Text
   Two modules are isomorphic if there is a surjection in each direction.
   These routines produce random combinations of the generators of Hom
   and test whether these are surjections.
SeeAlso
 isHomogeneouslyIsomorphic
 isLocallyIsomorphic
 surjectiveMap
///

doc ///
Key
 isHomogeneouslyIsomorphic
 (isHomogeneouslyIsomorphic, Module, Module)
Headline
 Tests homomogeneous isomorphism of graded modules
Usage
 t = isHomogeneouslyIsomorphic (A,B)
Inputs
 A:Module
 B:Module
Outputs
 t:Boolean
Description
  Text
  Example
   S = ZZ/32003[x_1..x_3]
   m = random(S^3, S^{4:-2})
   A = random(target m, target m)
   B = random(source m, source m)
   m' = A*m*B
   isHomogeneouslyIsomorphic (coker m, coker m')
   isLocallyIsomorphic(coker m, coker m')
Caveat
 To be isomorphic with this test the two modules have to be generated in the same degrees
SeeAlso
 isLocallyIsomorphic
///
-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

-* Development section *-
restart
debug needsPackage "Isomorphism"
check "Isomorphism"

restart
uninstallPackage "Isomorphism"
restart
installPackage "Isomorphism"
viewHelp "Isomorphism"
    
restart
