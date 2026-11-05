module

public import SHE.GaussianTaylor
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.AffineStateJets
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_affine {F : E→ℝ} (hF : Differentiable ℝ F) (L : D→L[ℝ]E) (m : E) (z : D) :
    fderiv ℝ (fun y => F (L y+m)) z=(fderiv ℝ F (L z+m)).comp L := by
  exact ((hF (L z+m)).hasFDerivAt.comp z (L.hasFDerivAt.add_const m)).fderiv

/-- The literal full Hessian chain rule for an affine observation map.
Both directions pass through the same displayed linear map. -/
theorem hessian_affine_apply {F : E→ℝ} (hF : ContDiff ℝ 2 F)
    (L : D→L[ℝ]E) (m : E) (z v w : D) :
    fderiv ℝ (fderiv ℝ (fun y => F (L y+m))) z v w=
      fderiv ℝ (fderiv ℝ F) (L z+m) (L v) (L w) := by
  have hDF : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have he : fderiv ℝ (fun y => F (L y+m))=(fun y => (fderiv ℝ F (L y+m)).comp L) := by
    funext y
    exact fderiv_affine (hF.differentiable (by norm_num)) L m y
  rw [he]
  have hc := (((hDF.differentiable (by norm_num)) (L z+m)).hasFDerivAt.comp z
    (L.hasFDerivAt.add_const m)).clm_comp (hasFDerivAt_const L z)
  simp only [Function.comp_def] at hc
  rw [hc.fderiv]
  simp

end SHE.AffineStateJets
