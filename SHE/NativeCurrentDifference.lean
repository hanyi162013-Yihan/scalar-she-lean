module

public import SHE.ControlledMeans
public import SHE.NativeHeatObservation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeCurrentDifference
open MeasureTheory NativeHeatObservation
open scoped ENNReal

/-! The corrected current cap in the ACTUAL native clock. The heat
age uses t/(2pi)^2 internally, whereas damping and past-time translation
retain the original physical t. -/

def currentDifference (Λ s τ : ℝ) (dCurrent dOld : DyadicApproximation.RealL2) : DyadicApproximation.RealL2 :=
  heat τ dCurrent-
    (Real.exp (-Λ*s)*(1-Real.exp (-Λ*τ))) • heat (s+τ) dOld

theorem currentDifference_norm {Λ s τ : ℝ} (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (dCurrent dOld : DyadicApproximation.RealL2) :
    ‖currentDifference Λ s τ dCurrent dOld‖ ≤ ‖dCurrent‖+‖dOld‖ := by
  have hr := ControlledMeans.remaining_damping_between hΛ hs hτ
  unfold currentDifference
  calc
    _ ≤ ‖heat τ dCurrent‖+
      ‖(Real.exp (-Λ*s)*(1-Real.exp (-Λ*τ))) • heat (s+τ) dOld‖ := norm_sub_le _ _
    _ ≤ ‖dCurrent‖+‖dOld‖ := by
      apply add_le_add (RealHeat.realHeat_contraction _ _)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hr.2).trans (RealHeat.realHeat_contraction _ _)

abbrev TimeL2 := Lp DyadicApproximation.RealL2 2 (volume : Measure ℝ)

def timeShift (s : ℝ) (D : TimeL2) : TimeL2 :=
  Lp.compMeasurePreserving (fun v : ℝ => v+s) (measurePreserving_add_right volume s) D

theorem timeShift_norm (s : ℝ) (D : TimeL2) : ‖timeShift s D‖ = ‖D‖ :=
  Lp.norm_compMeasurePreserving _ _

theorem timeShift_ae (s : ℝ) (D : TimeL2) :
    timeShift s D =ᵐ[volume] (fun v => D (v+s)) :=
  Lp.coeFn_compMeasurePreserving D (measurePreserving_add_right volume s)

def timeHeat (t : ℝ) (D : TimeL2) : TimeL2 := (heat t).compLp D

theorem timeHeat_ae (t : ℝ) (D : TimeL2) :
    timeHeat t D =ᵐ[volume] (fun v => heat t (D v)) := (heat t).coeFn_compLp D

theorem timeHeat_norm (t : ℝ) (D : TimeL2) : ‖timeHeat t D‖ ≤ ‖D‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(heat t).coeFn_compLp D] with v hv
  rw [show timeHeat t D v = heat t (D v) from hv]
  exact RealHeat.realHeat_contraction _ _

/-- The actual global-in-past-time current direction. Lebesgue translation
preserves the true L² norm, rather than replacing it by a pointwise or
spatial-supremum hypothesis. -/
def globalCurrentDifference (Λ s τ : ℝ) (D : TimeL2) : TimeL2 :=
  timeHeat τ (timeShift s D)-
    (Real.exp (-Λ*s)*(1-Real.exp (-Λ*τ))) • timeHeat (s+τ) D

theorem globalCurrentDifference_ae (Λ s τ : ℝ) (D : TimeL2) :
    globalCurrentDifference Λ s τ D =ᵐ[volume]
      (fun v => currentDifference Λ s τ (D (v+s)) (D v)) := by
  let r : ℝ := (Real.exp (-Λ*s)*(1-Real.exp (-Λ*τ)))
  filter_upwards [timeHeat_ae τ (timeShift s D), timeShift_ae s D,
    timeHeat_ae (s+τ) D, Lp.coeFn_sub (timeHeat τ (timeShift s D)) (r • timeHeat (s+τ) D),
    Lp.coeFn_smul r (timeHeat (s+τ) D)] with v hh hs hd hsub hsmul
  change (timeHeat τ (timeShift s D)-r • timeHeat (s+τ) D) v = _
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hh, hs, hd]
  rfl

theorem globalCurrentDifference_norm {Λ s τ : ℝ} (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (D : TimeL2) : ‖globalCurrentDifference Λ s τ D‖ ≤ 2 * ‖D‖ := by
  have hr := ControlledMeans.remaining_damping_between hΛ hs hτ
  unfold globalCurrentDifference
  calc
    _ ≤ ‖timeHeat τ (timeShift s D)‖+
      ‖(Real.exp (-Λ*s)*(1-Real.exp (-Λ*τ))) • timeHeat (s+τ) D‖ := norm_sub_le _ _
    _ ≤ ‖timeShift s D‖+‖D‖ := by
      apply add_le_add (timeHeat_norm _ _)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hr.2).trans (timeHeat_norm _ _)
    _ = _ := by rw [timeShift_norm]; ring

theorem globalCurrentDifference_sq {Λ s τ : ℝ} (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (D : TimeL2) : ‖globalCurrentDifference Λ s τ D‖ ^ 2 ≤ 4 * ‖D‖ ^ 2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (globalCurrentDifference_norm hΛ hs hτ D) 2
  nlinarith only [hh]

/-- The current-direction operation is an actual bounded linear map on
the integrated physical path space. -/
def globalCurrentOperator (Λ s τ : ℝ) : TimeL2 →L[ℝ] TimeL2 :=
  ((heat τ).compLpL 2 volume).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (fun v : ℝ => v+s)
      (measurePreserving_add_right volume s)).toContinuousLinearMap -
    (Real.exp (-Λ*s)*(1-Real.exp (-Λ*τ))) • (heat (s+τ)).compLpL 2 volume

theorem globalCurrentOperator_apply (Λ s τ : ℝ) (D : TimeL2) :
    globalCurrentOperator Λ s τ D = globalCurrentDifference Λ s τ D := rfl

theorem globalCurrentOperator_norm {Λ s τ : ℝ} (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    ‖globalCurrentOperator Λ s τ‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 2)
  intro D
  exact globalCurrentDifference_norm hΛ hs hτ D

/-- The global current cap holds for arbitrary random physical inputs.
The quantity on the right is their true expected integrated L² energy. -/
theorem random_current_energy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Λ s τ : ℝ} (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (D : Ω → TimeL2) (hD : MemLp D 2 μ) :
    MemLp (fun ω => globalCurrentDifference Λ s τ (D ω)) 2 μ ∧
      (∫ ω, ‖globalCurrentDifference Λ s τ (D ω)‖ ^ 2 ∂μ) ≤ 4 * ∫ ω, ‖D ω‖ ^ 2 ∂μ := by
  have hG : MemLp (fun ω => globalCurrentDifference Λ s τ (D ω)) 2 μ :=
    (globalCurrentOperator Λ s τ).comp_memLp' hD
  refine ⟨hG, ?_⟩
  have hiD := (memLp_two_iff_integrable_sq hD.norm.aestronglyMeasurable).mp hD.norm
  have hiG := (memLp_two_iff_integrable_sq hG.norm.aestronglyMeasurable).mp hG.norm
  calc
    _ ≤ ∫ ω, 4 * ‖D ω‖ ^ 2 ∂μ :=
      integral_mono hiG (hiD.const_mul 4) (fun ω => globalCurrentDifference_sq hΛ hs hτ (D ω))
    _ = _ := integral_const_mul _ _

end SHE.NativeCurrentDifference
