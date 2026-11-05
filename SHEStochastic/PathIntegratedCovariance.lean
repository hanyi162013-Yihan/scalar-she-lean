module

public import SHEStochastic.PastedGeneratorFunctional
public import SHEStochastic.PastedPastTests
public import SHEStochastic.FiniteItoTimeCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.PathIntegratedCovariance
open MeasureTheory StoppedPathPasting PastedGeneratorFunctional
open scoped NNReal

/-- Convert the native strictly-before time integral to its literal
real interval integral. Both deterministic endpoints are time-null. -/
theorem clock_before (H T : ℝ≥0) (hT : T ≤ H) (q : ℝ → ℝ) :
    (∫ r, (Set.Iio T).indicator (fun r : ℝ≥0 ↦ q (r : ℝ)) r
      ∂MathFin.ItoIntegralCLM.timeMeasure_T H) = ∫ r in (0 : ℝ)..(T : ℝ), q r := by
  let ν := MathFin.ItoIntegralCLM.timeMeasure_T H
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass ν := by dsimp [ν, MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  have he : (Set.Iio T).indicator (fun r : ℝ≥0 ↦ q (r : ℝ)) =ᵐ[ν]
      (Set.Ioc 0 T).indicator (fun r : ℝ≥0 ↦ q (r : ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := 0) (b := H)), ν.ae_ne T]
      with r hr hne
    have hiff : r ∈ Set.Iio T ↔ r ∈ Set.Ioc 0 T := by
      simp only [Set.mem_Iio, Set.mem_Ioc]
      exact ⟨fun h ↦ ⟨hr.1, h.le⟩, fun h ↦ lt_of_le_of_ne h.2 hne⟩
    simp only [Set.indicator_apply, hiff]
  rw [integral_congr_ae he]
  simpa only [NNReal.coe_zero] using FiniteItoTimeCalculus.clock_cell H 0 T zero_le hT q

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  (H : ℝ≥0)

/-- Deterministic time weights cover the integrating factors of the
Fourier martingales. The state covariance is already a bounded
continuous function, so its time integral is again bounded continuous
on path space. -/
def value (w : BoundedContinuousFunction ℝ ℝ) (b : BoundedContinuousFunction E ℝ)
    (x : Path H E) (t : Time H) : ℝ := ∫ s in 0..t.val, w s*b (read H x s)

theorem continuous_value (w : BoundedContinuousFunction ℝ ℝ) (b : BoundedContinuousFunction E ℝ) :
    Continuous (fun p : Path H E × Time H ↦ value H w b p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact (w.continuous.comp continuous_snd).mul
      (b.continuous.comp (continuous_eval.comp (continuous_fst.fst.prodMk
        ((continuous_projIcc (h := H.property)).comp continuous_snd))))
  · exact continuous_subtype_val.comp continuous_snd

theorem norm_bound (w : BoundedContinuousFunction ℝ ℝ) (b : BoundedContinuousFunction E ℝ)
    (x : Path H E) (t : Time H) : ‖value H w b x t‖ ≤ ‖w‖*‖b‖*H := by
  calc
    _ ≤ (‖w‖*‖b‖)*|t.val-0| := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ ↦ by
        rw [norm_mul]
        exact mul_le_mul (w.norm_coe_le_norm _) (b.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_mul_of_nonneg_left t.property.2 (by positivity)

def functional (w : BoundedContinuousFunction ℝ ℝ) (b : BoundedContinuousFunction E ℝ)
    (t : Time H) : BoundedContinuousFunction (Path H E) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ value H w b x t)
    ((continuous_value H w b).comp (continuous_id.prodMk continuous_const))
    (‖w‖*‖b‖*H) (fun x ↦ norm_bound H w b x t)

theorem usesPast (w : BoundedContinuousFunction ℝ ℝ) (b : BoundedContinuousFunction E ℝ)
    (t : Time H) : PastedPastTests.UsesPast H t (fun x ↦ value H w b x t) := by
  intro x y hxy
  apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
  intro s hs
  have hsH : s ∈ Set.Icc (0 : ℝ) (H : ℝ) := ⟨hs.1.le, hs.2.le.trans t.property.2⟩
  have he : read H x s = read H y s := by
    change read H x (⟨s, hsH⟩ : Time H).val = read H y (⟨s, hsH⟩ : Time H).val
    rw [read_val, read_val, hxy ⟨s, hsH⟩ hs.2.le]
  change w s*b (read H x s) = w s*b (read H y s)
  rw [he]

theorem difference_bound (w : BoundedContinuousFunction ℝ ℝ) (b c : BoundedContinuousFunction E ℝ)
    (x : Path H E) (t : Time H) :
    ‖value H w b x t-value H w c x t‖ ≤ ‖w‖*‖b-c‖*H := by
  have hb := (w.continuous.mul (b.continuous.comp (continuous_read H x))).intervalIntegrable (μ := volume) 0 t.val
  have hc := (w.continuous.mul (c.continuous.comp (continuous_read H x))).intervalIntegrable (μ := volume) 0 t.val
  have he : value H w b x t-value H w c x t = value H w (b-c) x t := by
    unfold value
    calc
      _ = ∫ s in 0..t.val, (w s*b (read H x s)-w s*c (read H x s)) :=
        (intervalIntegral.integral_sub hb hc).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro s _
        simp only [BoundedContinuousFunction.sub_apply]
        ring
  rw [he]
  exact norm_bound H w (b-c) x t

/-- The capped exponential changes no integrating factor at physical
times in the original horizon. Its global cap only bundles continuity. -/
def exponential (rate : ℝ) (hrate : 0 ≤ rate) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s ↦ Real.exp (min (max s 0) (H : ℝ)*rate))
    (Real.continuous_exp.comp (((continuous_id.max continuous_const).min continuous_const).mul_const rate))
    (Real.exp ((H : ℝ)*rate)) (fun s ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_right _ _) hrate))

theorem exponential_apply (rate : ℝ) (hrate : 0 ≤ rate) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (H : ℝ)) :
    exponential H rate hrate s = Real.exp (s*rate) := by
  change Real.exp (min (max s 0) (H : ℝ)*rate) = _
  rw [max_eq_left hs.1, min_eq_left hs.2]

end SHEStochastic.PathIntegratedCovariance
