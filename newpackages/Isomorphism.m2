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

isDegreeListZero = L -> 
-- test whether a list of lists has all entries of entries 0
   all(L, s -> 
           all(s,  e-> e === 0)); 

checkDegrees = method(Options =>{Verbose =>false})
checkDegrees(Module, Module) := o -> (A,B) -> (
    v := o.Verbose;
    if not isHomogeneous A and isHomogeneous B then error"Input modules not homogeneous";
    dA := sort degrees A;
    dB := sort degrees B;
    if #dA != #dB then (
	if v then <<"numbers of generators are different"<<endl;
	return()
	);
    degdiffs := for i from 0 to #dA-1 list dA_i-dB_i;
--error();
    if all(degdiffs, s-> s == degdiffs_0) then(
	if isDegreeListZero degdiffs  then (
	    if v then << "degree sequences are equal"<<endl;
            return {dA_0-dB_0};
	    );
    if v then <<"To make the degree sequences equal, tensor "<<A<<"with ring " << A << "to " << {dA_0-dB_0} <<endl;
    return {dA_0-dB_0}
    ) else
    if v then <<"degree sequences don't match"<<endl;
    )

///
restart
debug loadPackage "Isomorphism"
S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
A = S^{{2,1}}
B1 = S^{{1,1}}
B = S^{{1,1}, {2,3}}
checkDegrees(A,B)
d = checkDegrees(A,B1)
checkDegrees(B,B)
checkDegrees(S^d**A, B1)
///

surjectiveMap = method(Options => {Homogeneous => true})
surjectiveMap(Module,Module) := Sequence => o -> (A,B)->(
    S := ring A;
    H := Hom(A,B);
    Hp := prune H;
    pmap := Hp.cache.pruningMap;
    if o.Homogeneous then (
	d := min degrees Hp;
	f := homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^{-d})))) else
        f = homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^1)));
    	t := if o.Homogeneous and prune coker f == 0 or coker f == 0 then true else false;
    (t,f))
///
restart
errorDepth = 0
debug loadPackage "Isomorphism"
S = ZZ/101[a,b,Degrees => {{1,0},{0,1}}]
A = S^{{2,1}}
B1 = S^{{1,1}}
B = S^{{1,1}, {2,3}}
checkDegrees(A,B)
d = checkDegrees(A,B1)
checkDegrees(B,B)
checkDegrees(S^d**A, B1)
///


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
 checkDegrees
 (checkDegrees,Module,Module)
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
   This is to be used with isHomogeneouslyIsomorphic.
   
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
   d = checkDegrees(A,B)
   checkDegrees(S^d**A, C)
   checkDegrees(A,C)
   checkDegrees(B,B)
SeeAlso
 isHomogeneouslyIsomorphic
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
