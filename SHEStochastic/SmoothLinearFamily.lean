module

public import SHE.UniformSmooth
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SmoothLinearFamily
open SHE SHE.SmoothCylinders SHE.UniformSmooth
open scoped ContDiff

variable {P : Type*} {D E G : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Compact smooth tests satisfy the existing all-order bounded-smooth
interface directly by Mathlib's compact support derivative calculus. -/
theorem boundedSmooth_of_compact {F : E → G} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    BoundedSmooth F :=
  ⟨hF, fun k ↦ (hs.iteratedFDeriv (𝕜 := ℝ) k).exists_bound_of_continuous
    (hF.continuous_iteratedFDeriv (by simp))⟩

/-- Reuse the existing smooth linear pullback estimate with a varying
family of linear maps having one common operator norm bound. -/
theorem comp_family {F : P → E → G} (hF : UniformBoundedSmooth F)
    (L : P → D →L[ℝ] E) (K : ℝ) (hK : 0 ≤ K) (hL : ∀ p, ‖L p‖ ≤ K) :
    UniformBoundedSmooth (fun p z ↦ F p (L p z)) := by
  refine ⟨fun p ↦ (hF.boundedSmooth p).comp_right (L p) |>.smooth, fun k ↦ ?_⟩
  obtain ⟨M, hMn, hM⟩ := hF.bounds k
  refine ⟨M * K ^ k, mul_nonneg hMn (pow_nonneg hK _), fun p z ↦ ?_⟩
  change ‖iteratedFDeriv ℝ k (F p ∘ L p) z‖ ≤ _
  rw [(L p).iteratedFDeriv_comp_right (hF.smooth p) z (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (hM p (L p z)) (pow_le_pow_left₀ (norm_nonneg _) (hL p) k)
    (pow_nonneg (norm_nonneg _) _) hMn

end SHEStochastic.SmoothLinearFamily
