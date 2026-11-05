module

public import SHE.UniformSmooth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.UniformAffineSmooth
open UniformSmooth
open scoped ContDiff
variable {P : Type*} {D E G : Type}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Arbitrary varying affine centers preserve all state derivative
bounds. Varying linear maps require only their actual uniform operator
norm bound; no smoothness in the parameter is assumed here. -/
theorem comp_affine {F : P→E→G} (hF : UniformBoundedSmooth F)
    (L : P→D→L[ℝ]E) (m : P→E) {K : ℝ} (hK : 0≤K) (hL : ∀ p,‖L p‖≤K) :
    UniformBoundedSmooth (fun p z => F p (L p z+m p)) := by
  have hs : UniformBoundedSmooth (fun p y => F p (y+m p)) := by
    refine ⟨fun p => (hF.smooth p).comp (contDiff_id.add contDiff_const),fun k => ?_⟩
    obtain ⟨B,hB,hbound⟩ := hF.bounds k
    refine ⟨B,hB,fun p z => ?_⟩
    rw [iteratedFDeriv_comp_add_right]
    exact hbound p (z+m p)
  refine ⟨fun p => (hs.smooth p).comp (L p).contDiff,fun k => ?_⟩
  obtain ⟨B,hB,hbound⟩ := hs.bounds k
  refine ⟨B*K^k,mul_nonneg hB (pow_nonneg hK _),fun p z => ?_⟩
  change ‖iteratedFDeriv ℝ k ((fun y => F p (y+m p)) ∘ L p) z‖≤_
  rw [(L p).iteratedFDeriv_comp_right (hs.smooth p) z (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul (hbound p (L p z)) (pow_le_pow_left₀ (norm_nonneg _) (hL p) k)
    (pow_nonneg (norm_nonneg _) _) hB

end SHE.UniformAffineSmooth
