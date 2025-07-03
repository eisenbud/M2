------------------------------------------
-- FLINT ball arithmetic (formerly Arb) --
------------------------------------------

use gmp;

declarations "
	#ifdef HAVE_ARB_H
	# include <arb.h>
	# include <acb.h>
	#endif
	#ifdef HAVE_FLINT_ARB_H
	# include <flint/arb.h>
	# include <flint/acb.h>
	#endif
	";

header "
	#ifdef HAVE_ARB_H
	# include <arb_hypgeom.h>
	# include <acb_hypgeom.h>
	#endif
	#ifdef HAVE_FLINT_ARB_H
	# include <flint/arb_hypgeom.h>
	# include <flint/acb_hypgeom.h>
	#endif
	";

-- TODO: RRb and CCb at top level?

------------
-- RRb --
------------

export RRb := Pointer "arb_ptr";
init(x:RRb) ::= (
    Ccode(void, "arb_init(", x, ")");
    x);
newRRb():RRb := init(GCmalloc(RRb));
clear(x:RRb) ::= Ccode(void, "arb_clear(", x, ")");

export RRbcell := {+v:RRb, prec:ulong};

-- every RRbcell should be constructed using this so that it's finalized
export toRRbcell(x:RRb, prec:ulong):RRbcell := (
    y := RRbcell(x, prec);
    Ccode(void, "GC_REGISTER_FINALIZER(", y,
	", (GC_finalization_proc)arb_clear, ", y.v, ", 0, 0)");
    y);

-- clear after using
export toRRb(x:RR, y:RR, prec:ulong):RRb := (
    z := newRRb();
    Ccode(void, "arb_set_interval_mpfr(", z, ", ", x, ", ", y, ", ", prec, ")");
    z);
export toRRb(x:RR):RRb := toRRb(x, x, precision(x));
export toRRb(x:RRi):RRb := toRRb(leftRR(x), rightRR(x), precision(x));
export toRRb(x:ZZ, prec:ulong):RRb := (
    y := toRR(x);
    toRRb(y, y, prec));
export toRRb(x:QQ, prec:ulong):RRb := (
    y := toRR(x);
    toRRb(y, y, prec));

toRR(x:RRb, prec:ulong):RR := (
    y := newRRmutable(prec);
    Ccode(int, "arf_get_mpfr(", y, ", arb_midref(", x, "), MPFR_RNDN)");
    moveToRRandclear(y));

export toRRi(x:RRb, prec:ulong):RRi := (
    y := newRRimutable(prec);
    Ccode(void, "arb_get_interval_mpfr((mpfr_ptr)&", y,
	"->left, (mpfr_ptr)&", y, "->right, ", x, ")");
    moveToRRiandclear(y));

moveToRRiandclear(x:RRb, prec:ulong):RRi := (
    r := toRRi(x, prec);
    clear(x);
    r);

export midpoint(x:RRb, prec:ulong):RR := (
    y := newRRmutable(prec);
    Ccode(void, "arf_get_mpfr(", y, ", arb_midref(", x, "), MPFR_RNDN)");
    moveToRRandclear(y));

export radius(x:RRb):RR := (
    y := Ccode(double, "mag_get_d(arb_radref(", x, "))");
    -- radius is a mag_t, which always has precision 30
    toRR(y, ulong(30)));

export hash(x:RRb, prec:ulong):hash_t := (
    953 * hash(midpoint(x, prec)) + 277 * hash(radius(x)));

export tostringRRb(x:RRb):string := tostring(Ccode(charstar,
    "arb_get_str(", x, ", mpfr_get_str_ndigits(10, arb_bits(", x, ")), 0)"));

-- arithmetic
export RRbadd(x:RRb, y:RRb, prec:ulong):RRb := (
    z := newRRb();
    Ccode(void, "arb_add(", z, ", ", x, ", ", y, ", ", prec, ")");
    z);

-- special functions
export eint(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_hypgeom_ei(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export Gamma(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_gamma(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export Gamma(z:RRi,w:RRi):RRi := (
    prec := min(precision(z), precision(w));
    x := toRRb(z);
    y := toRRb(w);
    r := newRRb();
    Ccode(void, "arb_hypgeom_gamma_upper(", r, ", ", x, ", ", y, ", 0, ",
	prec, ")");
    clear(x);
    clear(y);
    moveToRRiandclear(r, prec));

export regularizedGamma(z:RRi,w:RRi):RRi := (
    prec := min(precision(z), precision(w));
    x := toRRb(z);
    y := toRRb(w);
    r := newRRb();
    Ccode(void, "arb_hypgeom_gamma_upper(", r, ", ", x, ", ", y, ", 1, ",
	prec, ")");
    clear(x);
    clear(y);
    moveToRRiandclear(r, prec));

export Digamma(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_digamma(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export lgamma(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_lgamma(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export zeta(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_zeta(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export erf(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_hypgeom_erf(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export erfc(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_hypgeom_erfc(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export inverseErf(x:RRi):RRi := (
    y := toRRb(x);
    r := newRRb();
    Ccode(void, "arb_hypgeom_erfinv(", r, ", ", y, ", ", precision(x), ")");
    clear(y);
    moveToRRiandclear(r, precision(x)));

export BesselJ(z:RRi,w:RRi):RRi := (
    prec := min(precision(z), precision(w));
    x := toRRb(z);
    y := toRRb(w);
    r := newRRb();
    Ccode(void, "arb_hypgeom_bessel_j(", r, ", ", x, ", ", y, ", ", prec, ")");
    clear(x);
    clear(y);
    moveToRRiandclear(r, prec));

export BesselY(z:RRi,w:RRi):RRi := (
    prec := min(precision(z), precision(w));
    x := toRRb(z);
    y := toRRb(w);
    r := newRRb();
    Ccode(void, "arb_hypgeom_bessel_y(", r, ", ", x, ", ", y, ", ", prec, ")");
    clear(x);
    clear(y);
    moveToRRiandclear(r, prec));

export Beta(z:RRi,w:RRi):RRi := (
    prec := min(precision(z), precision(w));
    x := toRRb(z);
    y := toRRb(w);
    v := toRRb(toRRi(1, prec));
    r := newRRb();
    Ccode(void, "arb_hypgeom_beta_lower(", r, ", ", x, ", ", y, ", ", v,
	 ", 0, ", prec, ")");
    clear(x);
    clear(y);
    moveToRRiandclear(r, prec));

export regularizedBeta(u:RRi,v:RRi,w:RRi):RRi := (
    prec := min(min(precision(u), precision(v)), precision(w));
    x := toRRb(u);
    y := toRRb(v);
    z := toRRb(w);
    r := newRRb();
    Ccode(void, "arb_hypgeom_beta_lower(", r, ", ", y, ", ", z, ", ", x,
	 ", 1, ", prec, ")");
    clear(x);
    clear(y);
    clear(z);
    moveToRRiandclear(r, prec));

------------
-- CCBall --
------------

export CCb := Pointer "acb_ptr";
init(z:CCb) ::= (
    Ccode(void, "acb_init(", z, ")");
    z);
newCCb():CCb := init(GCmalloc(CCb));
clear(z:CCb) ::= Ccode(void, "acb_clear(", z, ")");

export CCbcell := {+v:CCb, prec:ulong};

-- every CCbcell should be constructed using this so that it's finalized
export toCCbcell(x:CCb, prec:ulong):CCbcell := (
    y := CCbcell(x, prec);
    Ccode(void, "GC_REGISTER_FINALIZER(", y,
	", (GC_finalization_proc)acb_clear, ", y.v, ", 0, 0)");
    y);

-- clear after using
export toCCb(x:RRb, y:RRb):CCb := (
    z := newCCb();
    Ccode(void, "acb_set_arb_arb(", z, ", ", x, ", ", y, ")");
    z);

export toCCb(z:CC):CCb := (
    x := toRRb(realPart(z));
    y := toRRb(imaginaryPart(z));
    w := toCCb(x, y);
    clear(x);
    clear(y);
    w);

toCC(z:CCb, prec:ulong):CC := (
    x := Ccode(RRb, "acb_realref(", z, ")");
    y := Ccode(RRb, "acb_imagref(", z, ")");
    toCC(toRR(x, prec), toRR(y, prec)));

moveToCCandclear(z:CCb, prec:ulong):CC := (
    r := toCC(z, prec);
    clear(z);
    r);

export realPart(x:CCb):RRb := (
    y := newRRb();
    Ccode(void, "acb_get_real(", y, ", ", x, ")");
    y);

export imaginaryPart(x:CCb):RRb := (
    y := newRRb();
    Ccode(void, "acb_get_imag(", y, ", ", x, ")");
    y);

export tostringCCb(x:CCb):string := (
    tostringRRb(realPart(x)) + "+" + tostringRRb(imaginaryPart(x)) + "*ii");

export eint(z:CC):CC := (
    w := toCCb(z);
    r := newCCb();
    Ccode(void, "acb_hypgeom_ei(", r, ", ", w, ", ", precision(z), ")");
    clear(w);
    moveToCCandclear(r, precision(z)));

export Gamma(z:CC):CC := (
    w := toCCb(z);
    r := newCCb();
    Ccode(void, "acb_gamma(", r, ", ", w, ", ", precision(z), ")");
    clear(w);
    moveToCCandclear(r, precision(z)));

export Gamma(z:CC,w:CC):CC := (
    prec := min(precision(z), precision(w));
    x := toCCb(z);
    y := toCCb(w);
    r := newCCb();
    Ccode(void, "acb_hypgeom_gamma_upper(", r, ", ", x, ", ", y, ", 0, ",
	prec, ")");
    clear(x);
    clear(y);
    moveToCCandclear(r, prec));

export regularizedGamma(z:CC,w:CC):CC := (
    prec := min(precision(z), precision(w));
    x := toCCb(z);
    y := toCCb(w);
    r := newCCb();
    Ccode(void, "acb_hypgeom_gamma_upper(", r, ", ", x, ", ", y, ", 1, ",
	prec, ")");
    clear(x);
    clear(y);
    moveToCCandclear(r, prec));

export Digamma(z:CC):CC := (
    w := toCCb(z);
    r := newCCb();
    Ccode(void, "acb_digamma(", r, ", ", w, ", ", precision(z), ")");
    clear(w);
    moveToCCandclear(r, precision(z)));

export lgamma(z:CC):CC := (
    w := toCCb(z);
    r := newCCb();
    Ccode(void, "acb_lgamma(", r, ", ", w, ", ", precision(z), ")");
    clear(w);
    moveToCCandclear(r, precision(z)));

export zeta(z:CC):CC := (
    w := toCCb(z);
    r := newCCb();
    Ccode(void, "acb_zeta(", r, ", ", w, ", ", precision(z), ")");
    clear(w);
    moveToCCandclear(r, precision(z)));

export erf(z:CC):CC := (
    w := toCCb(z);
    r := newCCb();
    Ccode(void, "acb_hypgeom_erf(", r, ", ", w, ", ", precision(z), ")");
    clear(w);
    moveToCCandclear(r, precision(z)));

export erfc(z:CC):CC := (
    w := toCCb(z);
    r := newCCb();
    Ccode(void, "acb_hypgeom_erfc(", r, ", ", w, ", ", precision(z), ")");
    clear(w);
    moveToCCandclear(r, precision(z)));

export BesselJ(z:CC,w:CC):CC := (
    prec := min(precision(z), precision(w));
    x := toCCb(z);
    y := toCCb(w);
    r := newCCb();
    Ccode(void, "acb_hypgeom_bessel_j(", r, ", ", x, ", ", y, ", ", prec, ")");
    clear(x);
    clear(y);
    moveToCCandclear(r, prec));

export BesselY(z:CC,w:CC):CC := (
    prec := min(precision(z), precision(w));
    x := toCCb(z);
    y := toCCb(w);
    r := newCCb();
    Ccode(void, "acb_hypgeom_bessel_y(", r, ", ", x, ", ", y, ", ", prec, ")");
    clear(x);
    clear(y);
    moveToCCandclear(r, prec));

export Beta(z:CC,w:CC):CC := (
    prec := min(precision(z), precision(w));
    x := toCCb(z);
    y := toCCb(w);
    v := toCCb(toCC(1, prec));
    r := newCCb();
    Ccode(void, "acb_hypgeom_beta_lower(", r, ", ", x, ", ", y, ", ", v,
	 ", 0, ", prec, ")");
    clear(x);
    clear(y);
    moveToCCandclear(r, prec));

export regularizedBeta(u:CC,v:CC,w:CC):CC := (
    prec := min(min(precision(u), precision(v)), precision(w));
    x := toCCb(u);
    y := toCCb(v);
    z := toCCb(w);
    r := newCCb();
    Ccode(void, "acb_hypgeom_beta_lower(", r, ", ", y, ", ", z, ", ", x,
	 ", 1, ", prec, ")");
    clear(x);
    clear(y);
    clear(z);
    moveToCCandclear(r, prec));
