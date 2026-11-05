module

public import SHE.JointNativeDefect
public import SHE.HeatAgeContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeRowTargetContinuity
open MeasureTheory Set Filter FiniteHaar StoppedFourier NativeObservationCovariance
open scoped Topology ENNReal
local instance nativeRowTargetContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- Taking real coordinates is a genuine contraction on the complete
common Haar input, including vectors with infinitely many coordinates. -/
theorem realInputPart_lipschitz : LipschitzWith 1 realInputPart := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul]
  apply lp.norm_mono (by norm_num : (2:ENNReal)≠0)
  intro q
  change ‖(a q).re-(b q).re‖≤‖a q-b q‖
  simpa only [← Complex.sub_re,Real.norm_eq_abs] using Complex.abs_re_le_norm (a q-b q)

theorem row_continuousAt_target {ell M T r : ℝ} (hell : 0<ell)
    (f : EllipticField ell M) (hT : r<T) (x : HeatCircle) :
    ContinuousAt (fun s : ℝ => row hell f s r x) T := by
  have hc := (HeatAgeContinuity.continuousAt_circleHeat_age (sub_pos.mpr hT) x).comp
    (f := fun s : ℝ => s-r) (x := T) (continuous_id.sub continuous_const).continuousAt
  exact realInputPart_lipschitz.continuous.continuousAt.comp
    ((nativeFactorAnalysis f.1 ell M hell f.2.1 f.2.2).continuous.continuousAt.comp hc)

/-- Continuous changes of original stop and heat target preserve the
literal first-defect matrix whenever the heat ages remain positive. -/
theorem matrix_continuous {P : Type*} [TopologicalSpace P] {ell M : ℝ} (hell : 0<ell)
    {n : ℕ} (Λ : ℝ) (σ T : P→Fin n→ℝ) (x : Fin n→HeatCircle)
    (f g : EllipticField ell M) (r : ℝ)
    (hσ : ∀ i,Continuous (fun p => σ p i)) (hT : ∀ i,Continuous (fun p => T p i))
    (hgap : ∀ p i,r<T p i) :
    Continuous (fun p => JointNativeDefect.matrix hell Λ (σ p) (T p) x f g r) := by
  have hu (i : Fin n) : Continuous (fun p => row hell f (T p i) r (x i)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (row_continuousAt_target hell f (hgap p i) (x i)).comp (f := fun z => T z i) (x := p) (hT i).continuousAt
  have hv (i : Fin n) : Continuous (fun p => row hell g (T p i) r (x i)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (row_continuousAt_target hell g (hgap p i) (x i)).comp (f := fun z => T z i) (x := p) (hT i).continuousAt
  have he (i : Fin n) : Continuous (fun p => 1-Real.exp (-Λ*(σ p i-r))) :=
    continuous_const.sub (Real.continuous_exp.comp (((hσ i).sub continuous_const).const_mul (-Λ)))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((he i).mul (((hu i).sub (hv i)).inner (𝕜 := ℝ) (hv j))).add
    ((he j).mul ((hv i).inner (𝕜 := ℝ) ((hu j).sub (hv j))))).add
    (((he i).mul (he j)).mul (((hu i).sub (hv i)).inner (𝕜 := ℝ) ((hu j).sub (hv j))))

end SHE.NativeRowTargetContinuity
