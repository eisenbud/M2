needsPackage("LocalRings", FileName => "../LocalRings.m2")
load "mike-linkage.m2"
printWidth = 0

S = kk[x,y,z]
M0 = ideal((gens ideal"z2,x3,y4,xy2,x3y") * random(S^5, S^4))
assert not isHomogeneous M0
res (I = generalLink M0)
--tally for i to 100 list betti res (I = generalLink M0)

R = S_(ideal vars S)
J = I ** R

J = ideal map(R^1,R^{{-3}, {-3}, {-3}},{{x^2*y-12373*x^2-8521*y^2, x*y^2+5019*x*y+3216*y^2-13233*z^2+3723*x, 13424*x^2*y+936*x*y^2+10667*y*z^2+14913*x^2-8521*x*y-15541*y^2-12289*x}})
J = ideal map(R^1,R^{{-3}, {-3}, {-3}}, {{
	    x*y^2-2521*x*y+3380*y^2-7314*z^2-5316*x,
	    x^2*y-3016*x^2-3793*y^2,
	    -5866*x^2*y-492*x*y^2-12514*y*z^2-12634*x^2-3793*x*y+4895*y^2-10918*x }})
F' = chainComplex { gens J, syz gens J, syz syz gens J }
F = res J
F.dd

use S
M0 = monomialIdeal(x^3,x^2*y^2,x*y^3,y^4,x^2*y*z,x*y^2*z,z^5)
I = generalLink M0;
I2 = generalLink I;
elapsedTime F = res I2
J = I2 ** R
J = ideal map(R^1,R^{{-6}, {-6}, {-6}, {-6}, {-6}, {-5}},{{-1922*x*y*z^4-3584*y^2*z^4+27*x^5+724*x^4*z+6347*x^2*z^3+14457*x*y*z^3+409*y^2*z^3+12159*x^4-8388*x^3*z+2710*y^3*z+9220*x^2*z^2+9729*x*y*z^2+15176*y^2*z^2-14001*x^3+10304*x^2*y-11574*x*y^2-2207*y^3+11934*x^2*z-13406*x*y*z-5246*y^2*z-10581*x^2, x*y^6-1651*x^4*y*z^2-384*x*y^4*z^2-2409*y^5*z^2-1840*x^4*z^3+14498*x^3*y*z^3-7467*x*y^3*z^3-3076*y^4*z^3+586*x^4*y^2+12545*x^3*y^3+3389*x^2*y^4-583*x*y^5-9255*y^6-4674*x^4*y*z-11509*x^3*y^2*z-3491*x*y^4*z-4203*y^5*z+13887*x^4*z^2-316*x^3*y*z^2+15929*x^2*y^2*z^2-6467*x*y^3*z^2-11416*y^4*z^2-10361*x^3*z^3-10164*x^2*y*z^3-3084*x*y^2*z^3-13753*y^3*z^3-11075*y^2*z^4-5388*x^5-8816*x^4*y+2309*x^3*y^2+4965*x^2*y^3+6848*x*y^4-8543*y^5-9412*x^4*z-8327*x^3*y*z-6411*x^2*y^2*z-14302*x*y^3*z-3480*y^4*z+13531*x^3*z^2+882*x^2*y*z^2+866*x*y^2*z^2-2600*y^3*z^2+14454*x^2*z^3+2119*x*y*z^3-15858*y^2*z^3+12301*x*z^4+15850*y*z^4-15188*x^4+14028*x^3*y-10474*x^2*y^2-3432*x*y^3+12082*y^4-15682*x^3*z+10736*x^2*y*z-9069*x*y^2*z+13865*y^3*z+8906*x^2*z^2+708*x*y*z^2-2925*y^2*z^2+6173*x*z^3+7278*y*z^3-5613*x^3-269*x^2*y-3845*x*y^2-1103*y^3+6249*x^2*z-7966*x*y*z+255*y^2*z-12022*x*z^2+9420*y*z^2-12264*x^2+15094*x*y+8942*y^2+15976*x*z-15056*y*z, x^2*y^5+3322*x^4*y*z^2+3532*x*y^4*z^2-13005*y^5*z^2-9910*x^4*z^3-10136*x^3*y*z^3-3165*x*y^3*z^3+9476*y^4*z^3+1699*x^4*y^2-15504*x^3*y^3-2667*x^2*y^4-4356*x*y^5-1377*y^6+14803*x^4*y*z-7669*x^3*y^2*z+1331*x*y^4*z+12392*y^5*z-10506*x^4*z^2-10743*x^3*y*z^2+15459*x^2*y^2*z^2+15638*x*y^3*z^2+14603*y^4*z^2-5625*x^3*z^3-13024*x^2*y*z^3+3006*x*y^2*z^3+7390*y^3*z^3+15252*y^2*z^4+11867*x^5+9197*x^4*y-11484*x^3*y^2+11561*x^2*y^3+11316*x*y^4+6457*y^5-7971*x^4*z+2136*x^3*y*z+8679*x^2*y^2*z+5272*x*y^3*z-5639*y^4*z+3278*x^3*z^2+9073*x^2*y*z^2-5242*x*y^2*z^2+10136*y^3*z^2-10611*x^2*z^3+3502*x*y*z^3-13040*y^2*z^3-3629*x*z^4+6672*y*z^4+14145*x^4+6579*x^3*y+15264*x^2*y^2+8078*x*y^3-5401*y^4-6043*x^3*z-5770*x^2*y*z-972*x*y^2*z+6709*y^3*z+612*x^2*z^2-8876*x*y*z^2-893*y^2*z^2-1628*x*z^3+1237*y*z^3+9888*x^3+1868*x^2*y+6147*x*y^2-10549*y^3+3401*x^2*z+4111*x*y*z+5518*y^2*z-4781*x*z^2-10145*y*z^2-5112*x^2-1222*x*y-4173*y^2-10051*x*z-10595*y*z, x^3*y^4+13797*x^4*y*z^2+10114*x*y^4*z^2+14556*y^5*z^2+12471*x^4*z^3+9463*x^3*y*z^3-514*x*y^3*z^3-4354*y^4*z^3+2150*x^4*y^2+1341*x^3*y^3-1775*x^2*y^4+8922*x*y^5+14038*y^6-6097*x^4*y*z+5694*x^3*y^2*z+3697*x*y^4*z+105*y^5*z+10324*x^4*z^2-9750*x^3*y*z^2-5361*x^2*y^2*z^2+9181*x*y^3*z^2+455*y^4*z^2+12506*x^3*z^3+14738*x^2*y*z^3+11114*x*y^2*z^3+15183*y^3*z^3+1839*y^2*z^4-3134*x^5+15366*x^4*y-10612*x^3*y^2+12474*x^2*y^3+10147*x*y^4-15172*y^5+1436*x^4*z+10582*x^3*y*z+14655*x^2*y^2*z+8370*x*y^3*z+8718*y^4*z-15122*x^3*z^2+12756*x^2*y*z^2-1331*x*y^2*z^2-8680*y^3*z^2-14267*x^2*z^3-7810*x*y*z^3-15929*y^2*z^3-9017*x*z^4-4099*y*z^4-12681*x^4-10712*x^3*y+12099*x^2*y^2-7520*x*y^3-3514*y^4+12450*x^3*z+3361*x^2*y*z+1674*x*y^2*z-2228*y^3*z+15416*x^2*z^2-11652*x*y*z^2-9632*y^2*z^2+1540*x*z^3-3110*y*z^3-2055*x^3+9652*x^2*y+9847*x*y^2-4517*y^3-15847*x^2*z-12398*x*y*z-1594*y^2*z+3534*x*z^2+14003*y*z^2+4831*x^2-6558*x*y+10085*y^2+8460*x*z-14767*y*z, -5014*x^3*y^4-9615*x^2*y^5-11265*x*y^6+15064*x^4*y*z^2+13517*x*y^4*z^2-10749*y^5*z^2+5643*x^4*z^3+12811*x^3*y*z^3-6554*x*y^3*z^3-2398*y^4*z^3-1032*x^5*y+13887*x^4*y^2+3665*x^3*y^3+14312*x^2*y^4+3179*x*y^5+2482*y^6-9633*x^4*y*z-15223*x^3*y^2*z+4084*x*y^4*z+12802*y^5*z-10692*x^4*z^2-12436*x^3*y*z^2+11525*x^2*y^2*z^2+9095*x*y^3*z^2+1354*y^4*z^2+1303*x^3*z^3-7046*x^2*y*z^3-6378*x*y^2*z^3+10067*y^3*z^3-3749*x*y*z^4+15826*y^2*z^4+15739*x^5-10301*x^4*y+1670*x^3*y^2+13094*x^2*y^3-1075*x*y^4-10817*y^5-12592*x^4*z-1623*x^3*y*z-4055*x^2*y^2*z-4036*x*y^3*z-15162*y^4*z-564*x^3*z^2+9561*x^2*y*z^2+6231*x*y^2*z^2-6750*y^3*z^2+12144*x^2*z^3+1964*x*y*z^3+4404*y^2*z^3+1299*x*z^4-6031*y*z^4+1618*x^4-4166*x^3*y-13463*x^2*y^2-8573*x*y^3-12169*y^4-6463*x^3*z+6614*x^2*y*z+12358*x*y^2*z-14390*y^3*z-13912*x^2*z^2-10691*x*y*z^2+13834*y^2*z^2-15242*x*z^3+1951*y*z^3-3622*x^3+10635*x^2*y-2830*x*y^2+6365*y^3+13576*x^2*z-5052*x*y*z+2607*y^2*z+2248*x*z^2+14687*y*z^2-10898*x^2-12870*x*y+15249*y^2-925*x*z-13726*y*z, z^5+8923*y^3*z-15357*x^2*z^2-5424*x*y*z^2-13540*y^2*z^2+3604*x^3+5072*x^2*y+4650*x*y^2+7887*y^3+4787*x^2*z+3583*x*y*z-6124*y^2*z-8411*x^2}})
-- takes about 10s for the ideal above
elapsedTime F = res J
-- elapsedTime F' = chainComplex { gens J, syz gens J, syz syz gens J }

f0 = J_1
phi0 = map(F_0, F_0, f0 * id_(F_0))
s0 = phi0 // F.dd_1
assert(F.dd_1 * s0 == phi0)


--- this is the slow step: ---
phi1 = map(F_1, F_1, f0 * id_(F_1))
syz liftUp((phi1 - s0 * F.dd_1) | F.dd_2)


phi1 = map(F_1, F_1, f0 * id_(F_1))
s1 = (phi1 - s0 * F.dd_1) // F.dd_2
assert(F.dd_2 * s1 == phi1 - s0 * F.dd_1)

phi2 = map(F_2, F_2, f0 * id_(F_2))
s2 = (phi2 - s1 * F.dd_2) // F.dd_3
assert(F.dd_3 * s2 == phi2 - s1 * F.dd_2)

phi3 = map(F_3, F_3, f0 * id_(F_3))
s3 = (phi3 - s2 * F.dd_3) // F.dd_4
assert(F.dd_4 * s3 == phi3 - s2 * F.dd_3)

L = {s0, s1, s2, s3}
phi = map(F, F, i -> L#i, Degree => 1)
phi = map(F[1], F, i -> L#i)

needsPackage "Complexes"
F' = complex F
map(F', F', i -> L#i, Degree => 1)
map(F'[1], F', i -> L#i)
phi' = map(F'[1], F', L)
phi' = map(F', F', L, Degree => 1)
-- FIXME
isCommutative phi'
errorDepth=2
-- FIXME
isNullHomotopic phi'


end--
restart
errorDepth=2
needs "homotopy.m2"

assert(F.dd_2 * s1 == phi1 - s0 * F.dd_1) -- FIXED

-- tracking the problem
A = F.dd_2 * s1
F'.dd_2 * L#1
B = s0 * F.dd_1
A + B
C = (A + B)_{1}

s1_0
F.dd_2 * s1_0 + B_0
F.dd_2^{0} * s1_0
F.dd_2^{1} * s1_0
F.dd_2^{2} * s1_0

-- here is the issue
s1_1
F.dd_2 * s1_1 + B_1
F.dd_2^{0} * s1_1
F.dd_2^{1} * s1_1
F.dd_2^{2} * s1_1

errorDepth = 1
quotient(phi1 - s0 * F.dd_1, F.dd_2)

f = phi1 - s0 * F.dd_1
g = F.dd_2

-- Here is the cause of the first problem: this matrix is not column reduced
G = syz(f | g)
G_1 - (14120_R^-1*14120) * G_1
G_2 - (14120_R^-1*7556) * G_1

G0 = mutableMatrix (syz liftUp(f | g) ** R)
G = G0

i = 1

C = f_{i}
n = scan(numColumns G, j -> if isUnit G_(i,j) then break j)
u = -G_(i, n)^-1
C = u * matrix submatrix(G, {numColumns f..numRows G-1}, {n})
scan(n+1 .. numColumns G-1, j -> columnAdd(G, j, u * G_(i,j), n))
-- TODO: is this step necessary? simplify above and remove this
G = submatrix(G, ,{0..n-1, n+1..numColumns G-1})
C_0

F.dd_2 * C_0

E = syz(f_{1} | g)
E = syz(f_{1}^{0} | g^{0})
E' = (14120*y+10073)_R^-1 * E_1^{1..3}
g * E' + B_1

E = syz(f_{2} | g)
E = syz(f_{2}^{0} | g^{0})
E' = -(11679*y+11439)_R^-1 * E_1^{1..3}
g * E' + B_2


-- old, bad value
s' = -9184_R^-1 * vector{0,0,1_R}
g * s' + B_1
