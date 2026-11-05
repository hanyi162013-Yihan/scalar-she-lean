module

public import SHE.PredictableContraction
public import SHE.TwoChannelItoRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.PredictableWeightedAlgebra
open MeasureTheory PredictableL2 PredictableContraction OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
variable (a : ℝ≥0×Ω→ℝ) (ha : StronglyMeasurable[𝓕.predictable] a) (hb : ∀ p,|a p|≤1)

theorem weighted_sub (v w : Process (E := C) 𝓕 μ h) :
    weighted 𝓕 μ h a ha hb (v-w)=weighted 𝓕 μ h a ha hb v-weighted 𝓕 μ h a ha hb w := by
  apply Lp.ext
  filter_upwards [(weighted_memLp 𝓕 μ h a ha hb (v-w)).coeFn_toLp,
    (weighted_memLp 𝓕 μ h a ha hb v).coeFn_toLp,
    (weighted_memLp 𝓕 μ h a ha hb w).coeFn_toLp,Lp.coeFn_sub v w,
    Lp.coeFn_sub (weighted 𝓕 μ h a ha hb v) (weighted 𝓕 μ h a ha hb w)] with p hs hv hw hi ho
  change weighted 𝓕 μ h a ha hb (v-w) p=_
  change weighted 𝓕 μ h a ha hb (v-w) p=a p • (v-w) p at hs
  change weighted 𝓕 μ h a ha hb v p=a p • v p at hv
  change weighted 𝓕 μ h a ha hb w p=a p • w p at hw
  rw [hs,ho]
  change a p • (v-w) p=weighted 𝓕 μ h a ha hb v p-weighted 𝓕 μ h a ha hb w p
  rw [hi,hv,hw]
  exact smul_sub _ _ _

section Block
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
local instance predictableWeightedAlgebra_blockSigma : MeasurableSpace (Both C) := borel _
local instance predictableWeightedAlgebra_blockBorel : BorelSpace (Both C) := ⟨rfl⟩

theorem weighted_block (v w : Process (E := C) 𝓕 μ h) :
    weighted 𝓕 μ h a ha hb (TwoChannelItoRows.block 𝓕 μ h v w)=
      TwoChannelItoRows.block 𝓕 μ h (weighted 𝓕 μ h a ha hb v) (weighted 𝓕 μ h a ha hb w) := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [weighted_ae 𝓕 μ h a ha hb (TwoChannelItoRows.block 𝓕 μ h v w),
    TwoChannelItoRows.block_ae 𝓕 μ h v w,weighted_ae 𝓕 μ h a ha hb v,
    weighted_ae 𝓕 μ h a ha hb w,
    TwoChannelItoRows.block_ae 𝓕 μ h (weighted 𝓕 μ h a ha hb v) (weighted 𝓕 μ h a ha hb w)]
    with p hs hi hv hw ho
  rw [hs,hi,ho,hv,hw]
  apply WithLp.ofLp_injective
  rfl

end Block
end SHE.PredictableWeightedAlgebra
