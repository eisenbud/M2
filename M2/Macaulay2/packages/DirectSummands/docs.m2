-- TODO:
-- [x] example that is indecomposable
-- [ ] example that decomposes after field extension
-- [ ] example over ZZ, ZZ[i]/(i^2+1), QQ, QQ[i]/(i^2+1), GF, RR, CC?
-- [ ] graded example
-- [ ] local example
-- [ ] example of passing hints of summands
-- [ ] example of isIndecomposable

doc ///
Node
  Key
    DirectSummands
  Headline
    decompositions of graded modules and coherent sheaves
  Description
    Text
      As an example, we prove the indecomposability of the @wikipedia "Horrocks–Mumford bundle"@ on $\PP^4$.
    Example
      needsPackage "BGG"
      S = ZZ/32003[x_0..x_4];
      E = ZZ/32003[e_0..e_4, SkewCommutative => true];
      alphad = map(E^5, E^{-2,-2}, transpose matrix{
	      { e_1*e_4, -e_0*e_2, -e_1*e_3, -e_2*e_4,  e_0*e_3},
	      {-e_2*e_3, -e_3*e_4,  e_0*e_4, -e_0*e_1, -e_1*e_2}});
      alpha = syz alphad;
      alphad = beilinson(alphad, S);
      alpha = beilinson(alpha, S);
      FHM = prune homology(alphad, alpha)
      assert(2 == rank FHM)
      -- initially ~30s for End(FHM), ~110s for basis; ~35s in ZZ/2; now down to ~1s total!
      assert({FHM} == summands FHM)
      assert FHM.cache.isIndecomposable
  Acknowledgement
    The authors thank the organizers of the @HREF{"https://aimath.org/pastworkshops/macaulay2efie.html",
	"Macaulay2 workshop at AIM"}@, where significant progress on this package was made.
  References
    @HREF{"https://doi.org/10.1016/j.jsc.2025.102486", "Computing direct sum decompositions"}@,
    Mallory and Sayrafi, Journal of Symbolic Computation, Volume 133, March–April 2026
    @HREF{"https://arxiv.org/abs/2412.19799v2", "[arXiv:2412.19799]"}@.
  Subnodes
    directSummands
  Citation
    @article{MS26,
      author       = {Mallory, Devlin and Sayrafi, Mahrud},
      title	       = {Computing direct sum decompositions},
      journal      = {J. Symbolic Comput.},
      fjournal     = {Journal of Symbolic Computation},
      volume       = {133},
      year	       = {2026},
      doi	       = {10.1016/j.jsc.2025.102486},
    }

Node
  Key
    directSummands
    (directSummands, Module)
    (directSummands, CoherentSheaf)
  Headline
    computes the direct summands of a graded module or coherent sheaf
  Usage
    summands M
  Inputs
    M:{Module,CoherentSheaf}
  Outputs
    :List
      containing modules or coherent sheaves which are direct summands of $M$
  Description
    Text
      This function attempts to find the indecomposable summands of a module or coherent sheaf $M$.
    Example
      S = QQ[x,y]
      M = coker matrix{{x,y},{x,x}}
      L = summands M
      assert isIsomorphic(M, directSum L)
  SeeAlso
    findIdempotents
///

-- Template:
///
Node
  Key
  Headline
  Usage
  Inputs
  Outputs
  Consequences
    Item
  Description
    Text
    Example
    CannedExample
    Code
    Pre
  ExampleFiles
  Contributors
  References
  Caveat
  SeeAlso
--    Tree
--    CannedExample
--  Contributors
--  References
--  Caveat
--  SeeAlso
///
