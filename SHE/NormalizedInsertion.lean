module

public import SHE.CutoffInsertionCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.NormalizedInsertion
open MeasureTheory WordRecursion GaussianTaylor GaussianSmooth CutoffInsertionCore
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def unitRow (r : E) : E := ‖r‖⁻¹ • r

theorem norm_unitRow_le (r : E) : ‖unitRow r‖ ≤ 1 := by
  by_cases hr : r=0
  · simp [unitRow,hr]
  · exact (norm_smul_inv_norm (𝕜 := ℝ) hr).le

theorem norm_smul_unitRow (r : E) : ‖r‖ • unitRow r=r := by
  by_cases hr : r=0
  · simp [unitRow,hr]
  · rw [unitRow,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr),one_smul]

theorem measurable_unitRow [MeasurableSpace E] [BorelSpace E] : Measurable (unitRow (E := E)) :=
  measurable_id.norm.inv.smul measurable_id

theorem average_smul [MeasurableSpace E] (μ : Measure E) (w : ℝ) (F : E → ℝ) :
    GaussianSmooth.average μ (w • F)=w • GaussianSmooth.average μ F := by
  funext z
  exact integral_smul w (fun y => F (z+y))

theorem hessian_smul (w : ℝ) (F : E → ℝ) :
    GaussianTaylor.hessian (w • F)=w • GaussianTaylor.hessian F := by
  funext z
  change fderiv ℝ (fderiv ℝ (w • F)) z=w • fderiv ℝ (fderiv ℝ F) z
  rw [fderiv_const_smul_field]
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ F) w) z

theorem core_smul_test {n : ℕ} (a : ℝ → ℝ) (c w : ℝ) (r : WordRecursion.State n) (F : WordRecursion.State n → ℝ) :
    core a c r (w • F)=w • core a c r F := by
  funext z
  change (1/2:ℝ)*(a (z 0)-c)*GaussianTaylor.hessian (w • F) (SmoothWords.tailProjection n z) r r=_
  rw [hessian_smul]
  simp only [Pi.smul_apply,smul_apply,smul_eq_mul]
  change _=w*((1/2:ℝ)*(a (z 0)-c)*GaussianTaylor.hessian F (SmoothWords.tailProjection n z) r r)
  ring

theorem core_smul_row {n : ℕ} (a : ℝ → ℝ) (c w : ℝ) (r : WordRecursion.State n) (F : WordRecursion.State n → ℝ) :
    core a c (w • r) F=(w^2) • core a c r F := by
  funext z
  unfold core WordRecursion.directionalSecond
  simp only [map_smul,smul_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Exact row normalization factors out its true squared Hilbert norm.
No heat-gap estimate or positive lower norm is imposed. -/
theorem core_weighted_unitRow {n : ℕ} (a : ℝ → ℝ) (c w : ℝ) (r : WordRecursion.State n) (F : WordRecursion.State n → ℝ) :
    core a c r (w • F)=(w*‖r‖^2) • core a c (unitRow r) F := by
  rw [core_smul_test]
  have hr := congrArg (fun q => core a c q F) (norm_smul_unitRow r)
  rw [core_smul_row] at hr
  rw [← hr,smul_smul]

end SHE.NormalizedInsertion
