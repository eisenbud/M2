#include "aring-CCi.hpp"

namespace M2 {

void ARingCCi::text_out(buffer &o) const { o << "ACCi_" << mPrecision; }
void ARingCCi::elem_text_out(buffer &o,
                             const ElementType &ap,
                             bool p_one,
                             bool p_plus,
                             bool p_parens) const
{
//  cci_struct a = &const_cast<ElementType &>(&ap);
  M2_string s1 = (*gmp_tostringRRpointer)(&(ap.re.left));
  M2_string s2 = (*gmp_tostringRRpointer)(&(ap.re.right));
  M2_string s3 = (*gmp_tostringRRpointer)(&(ap.im.left));
  M2_string s4 = (*gmp_tostringRRpointer)(&(ap.im.right));

  if(p_plus) o << "+";
  o << "[";
  o.put((char *)s1->array, s1->len);
  o << ",";
  o.put((char *)s2->array, s2->len);
  o << "]+[";
  o.put((char *)s3->array, s3->len);
  o << ",";
  o.put((char *)s4->array, s4->len);
  o << "]i";
}

};  // end namespace M2

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e  "
// indent-tabs-mode: nil
// End:
