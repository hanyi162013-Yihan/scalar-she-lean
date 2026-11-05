module

public import SHE.NativeColumnHeatSemigroup

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.RealHaarSemigroup
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.NativeHeatObservation

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Exact heat propagation of the actual countable real Haar columns
in the normalized circle clock. No upper bound on either time occurs. -/
theorem map_kernel {ell cap s t : ℝ} (hell : 0 < ell) (hs : 0 ≤ s) (ht : 0 < t)
    (f : EllipticField ell cap) :
    HilbertColumns.mapCLM (RealHeat.realHeat s) (RealHaarIntegrand.kernel ell cap hell (t,f)) =
      RealHaarIntegrand.kernel ell cap hell (s+t,f) := by
  apply lp.ext
  funext i
  change RealHeat.realHeat s (RealHaarIntegrand.kernel ell cap hell (t,f) i) =
    RealHaarIntegrand.kernel ell cap hell (s+t,f) i
  apply realCircleIdentification.injective
  apply Subtype.ext
  change realEmbed (RealHeat.realHeat s (RealHaarIntegrand.kernel ell cap hell (t,f) i)) =
    realEmbed (RealHaarIntegrand.kernel ell cap hell (s+t,f) i)
  rw [RealHeat.realEmbed_realHeat, RealHaarIntegrand.kernel_apply, RealHaarIntegrand.kernel_apply,
    realEmbed_realPart_of_real _ (RealHaarIntegrand.kernel_column_real hell _ i),
    realEmbed_realPart_of_real _ (RealHaarIntegrand.kernel_column_real hell _ i),
    HaarHeatIntegrand.kernel_apply, HaarHeatIntegrand.kernel_apply,
    if_pos ht, if_pos (add_pos_of_nonneg_of_pos hs ht), CircleHeat.heat_semigroup hs ht.le]
  rfl

end SHEStochastic.RealHaarSemigroup
