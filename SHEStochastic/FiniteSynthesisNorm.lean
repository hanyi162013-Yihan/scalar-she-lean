module

public import SHEStochastic.FiniteSynthesisBessel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FiniteSynthesisNorm
open FiniteSynthesisBessel

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The common finite-column Bessel construction retains its exact
operator norm bound when extended to the full coefficient `ℓ²` space. -/
theorem bound (a : ι → E) (U : ℝ) (hU : 0 ≤ U)
    (hFinite : ∀ (s : Finset ι) (z : ι → ℝ),
      ‖∑ i∈s, z i • a i‖^2 ≤ U*(∑ i∈s, ‖z i‖^2)) :
    ‖synthesis a U hU hFinite‖ ≤ Real.sqrt U := by
  let T := SHE.BesselSynthesis.analysis a (summable a U hU hFinite) U hU (tsum_bound a U hU hFinite)
  have ht : ‖T‖ ≤ Real.sqrt U := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg U)
    intro x
    have hh := tsum_bound a U hU hFinite x
    rw [← SHE.BesselSynthesis.analysis_norm_sq a (summable a U hU hFinite)
      U hU (tsum_bound a U hU hFinite)] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg U) (norm_nonneg _))).mp
    rwa [mul_pow, Real.sq_sqrt hU]
  change ‖T.adjoint‖ ≤ Real.sqrt U
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact ht

end SHEStochastic.FiniteSynthesisNorm
