import PassantCodeQ13.MinimumWords.RowUniqueness.Base

/-!
# Injectivity of support decoding

The 364 encoded supports remain distinct after transport to semantic internal-point sets.
-/

namespace PassantCodeQ13.MinimumWords.RowUniqueness

/-- Decoding is injective on the four-orbit support list. -/
theorem decodedSupport_injOn :
    Set.InjOn decodedSupport minimumSupportCodes.toFinset :=
  decodedSupport_injOn_of_check (by native_decide)

end PassantCodeQ13.MinimumWords.RowUniqueness
