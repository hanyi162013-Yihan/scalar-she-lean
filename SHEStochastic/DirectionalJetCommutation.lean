module

public import SHEStochastic.DirectionalJets
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.DirectionalJets
open Filter
open scoped Topology ContDiff
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem commute {f : E → A} {x : E} (hf : ContDiffAt ℝ 2 f x) (v a : E) :
    directional v (directional a f) x = directional a (directional v f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (b : E) : fderiv ℝ (directional b f) x =
      (ContinuousLinearMap.apply ℝ A b).comp (fderiv ℝ (fderiv ℝ f) x) := by
    exact ((ContinuousLinearMap.apply ℝ A b).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  simp only [directional, he, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact hf.isSymmSndFDerivAt (by norm_num) v a

/-- Differentiating an actual mixed jet at its base point commutes
with all prior directions, by the ordinary real second derivative
symmetry theorem. No analyticity assumption is needed. -/
theorem directional_jet {f : E → A} {x : E} (hf : ContDiffAt ℝ ∞ f x) (w : List E) (v : E) :
    directional v (jet w f) x = jet (v :: w) f x := by
  induction w generalizing f with
  | nil => rfl
  | cons a w ih =>
    change directional v (jet w (directional a f)) x = jet w (directional a (directional v f)) x
    rw [ih (directional_smooth hf a)]
    apply congr w
    have h2 : ContDiffAt ℝ 2 f x := hf.of_le (by simp)
    filter_upwards [h2.eventually (by norm_num)] with y hy
    exact commute hy v a

theorem hasDerivAt_line {f : E → A} (x v : E) (s : ℝ)
    (hf : ContDiffAt ℝ ∞ f (x + s • v)) (w : List E) :
    HasDerivAt (fun r : ℝ => jet w f (x + r • v)) (jet (v :: w) f (x + s • v)) s := by
  have hl : HasDerivAt (fun r : ℝ => x + r • v) v s := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const v).const_add x
  have hh := ((smooth w hf).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hl
  have he := directional_jet hf w v
  change fderiv ℝ (jet w f) (x + s • v) v = _ at he
  rw [he] at hh
  exact hh

end SHEStochastic.DirectionalJets
