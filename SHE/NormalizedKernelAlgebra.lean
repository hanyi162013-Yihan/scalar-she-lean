module

public import SHE.NormalizedKernelSplit
public import SHE.NativeKernelAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NormalizedKernelSplit
open MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel
open scoped ENNReal
local instance normalizedKernelAlgebra_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact operator splitting takes place before every right heat/noise
factor, so the bad amplitude is never moved onto the signed input. -/
theorem fullOperator_eq_good_add_bad {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B) (R : ℝ) (ω : Ω) :
    integralOperator (fullKernel H A) ω=
      integralOperator (goodKernel H A R) ω+integralOperator (badKernel H A R) ω := by
  apply integralOperator_eq_add (fullKernel_measurable hH hA) (goodKernel_measurable hH hA R)
    (badKernel_measurable hH hA R) hB hb (goodKernel_bound hB hb R) (badKernel_bound hB hb R)
  intro ω y x
  exact (sub_add_cancel (fullKernel H A (ω,(y,x))) (badKernel H A R (ω,(y,x)))).symm

theorem full_action_eq_good_add_bad {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B) (R : ℝ) (ω : Ω)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : CircleL2 →L[ℂ] E) (v : CircleL2) :
    Q (integralOperator (fullKernel H A) ω v)=
      Q (integralOperator (goodKernel H A R) ω v)+Q (integralOperator (badKernel H A R) ω v) := by
  rw [fullOperator_eq_good_add_bad hH hA hB hb R ω,ContinuousLinearMap.add_apply,map_add]

/-- The full, good and bad columns are the true columns with the same
right input; the square-sum inequality follows from that exact identity. -/
theorem full_column_sq_le {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B) (R : ℝ) (ω : Ω)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : CircleL2 →L[ℂ] E) (v : CircleL2) :
    ‖Q (integralOperator (fullKernel H A) ω v)‖^2 ≤
      2*‖Q (integralOperator (goodKernel H A R) ω v)‖^2+
        2*‖Q (integralOperator (badKernel H A R) ω v)‖^2 := by
  rw [full_action_eq_good_add_bad hH hA hB hb R ω Q v]
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (norm_add_le (Q (integralOperator (goodKernel H A R) ω v))
      (Q (integralOperator (badKernel H A R) ω v))) 2
  nlinarith [sq_nonneg (‖Q (integralOperator (goodKernel H A R) ω v)‖-
    ‖Q (integralOperator (badKernel H A R) ω v)‖)]

theorem full_trace_le_good_bad {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B) (R : ℝ) (ω : Ω)
    {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : CircleL2 →L[ℂ] E) (v : N → CircleL2)
    (hgood : Summable (fun n => ‖Q (integralOperator (goodKernel H A R) ω (v n))‖^2))
    (hbad : Summable (fun n => ‖Q (integralOperator (badKernel H A R) ω (v n))‖^2)) :
    Summable (fun n => ‖Q (integralOperator (fullKernel H A) ω (v n))‖^2) ∧
      (∑' n, ‖Q (integralOperator (fullKernel H A) ω (v n))‖^2) ≤
        2*(∑' n, ‖Q (integralOperator (goodKernel H A R) ω (v n))‖^2)+
          2*(∑' n, ‖Q (integralOperator (badKernel H A R) ω (v n))‖^2) := by
  have hmajor := (hgood.mul_left 2).add (hbad.mul_left 2)
  have hp (n : N) := full_column_sq_le hH hA hB hb R ω Q (v n)
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hp hmajor
  refine ⟨hs,?_⟩
  have hh := hs.tsum_le_tsum hp hmajor
  rw [(hgood.mul_left 2).tsum_add (hbad.mul_left 2),tsum_mul_left,tsum_mul_left] at hh
  exact hh

end SHE.NormalizedKernelSplit
