import PassantCodeQ13.Automorphisms.Base

/-!
# Separation by four-anchor signatures

The four polar values relative to the displayed anchors, with equality recorded separately from a
relation value, distinguish all 78 internal points.  Kernel reduction checks injectivity on the
complete coordinate set.
-/

namespace PassantCodeQ13.Automorphisms

/-- Four-anchor signatures distinguish every indexed internal point. -/
theorem anchorSignature_injective : Function.Injective anchorSignature := by
  decide +kernel

end PassantCodeQ13.Automorphisms
