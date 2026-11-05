module

public import SHEStochastic.HeatParameterCoordinates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HeatParameterPullback
open MeasureTheory HeatParameterCover HeatParameterCoordinates SHE SHE.StoppedFourier SHE.NativeHeatSpan
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev ShortTime := Set.Icc (0 : ℝ) 1

def initialTime : ShortTime := ⟨0, le_rfl, zero_le_one⟩

/-- A measurable spatial coordinate in the unit interval. Continuity
of this representative at the circle seam is not needed. -/
def representative (a : HeatCircle) : ℝ :=
  (AddCircle.measurableEquivIco (T := 1) 0 (unitCenter a)).val

theorem representative_mem (a : HeatCircle) : representative a ∈ Set.Ico (0 : ℝ) 1 := by
  have hh := (AddCircle.measurableEquivIco (T := 1) 0 (unitCenter a)).property
  exact ⟨hh.1, hh.2.trans_eq (zero_add (1 : ℝ))⟩

theorem measurable_representative : Measurable representative :=
  measurable_subtype_coe.comp ((AddCircle.measurableEquivIco (T := 1) 0).measurable.comp
    (CircleNormalization.continuous_scale (2 * Real.pi) 1).measurable)

/-- Embed an actual time and physical-circle point in the compact
parameter domain used by the convolution continuity theorem. -/
def point (t : ShortTime) (a : HeatCircle) : Parameter :=
  ⟨PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 0 t.val + PiLp.single 2 1 (representative a), by
    change _ ∈ Metric.closedEBall (0 : Plane) (2 : ℝ≥0)
    rw [Metric.closedEBall_coe, Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ ‖PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 0 t.val‖ +
          ‖PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 1 (representative a)‖ := norm_add_le _ _
      _ = t.val + representative a := by
        rw [PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg t.property.1, abs_of_nonneg (representative_mem a).1]
      _ ≤ 2 := by linarith [t.property.2, (representative_mem a).2]⟩

@[simp] theorem point_time (t : ShortTime) (a : HeatCircle) : (point t a).val 0 = t.val := by
  simp [point]

@[simp] theorem point_space (t : ShortTime) (a : HeatCircle) : (point t a).val 1 = representative a := by
  simp [point]

theorem time_point (H : ℝ≥0) (t : ShortTime) (a : HeatCircle) (ht : t.val ≤ H) :
    (time H (point t a)).val = t.val := by
  change min (max ((point t a).val 0) 0) (min (H : ℝ) 1) = t.val
  rw [point_time, max_eq_left t.property.1, min_eq_left (le_min ht t.property.2)]

theorem center_point (t : ShortTime) (a : HeatCircle) : center (point t a) = a := by
  apply (CircleNormalization.scale (2 * Real.pi) 1).injective
  change unitCenter (center (point t a)) = unitCenter a
  rw [unit_center, point_space]
  exact AddCircle.coe_equivIco

theorem zeroTime_point (t : ShortTime) (a : HeatCircle) :
    HeatParameterCoordinates.zeroTime (point t a) = point initialTime a := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [HeatParameterCoordinates.zeroTime, point, initialTime]

theorem point_distance (t s : ShortTime) (a : HeatCircle) :
    dist (point t a) (point s a) = |t.val - s.val| := by
  have hv : (point t a).val - (point s a).val =
      PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 0 (t.val - s.val) := by
    ext i
    fin_cases i <;> simp [point]
  change ‖(point t a).val - (point s a).val‖ = _
  rw [hv, PiLp.norm_single, Real.norm_eq_abs]

theorem measurable_point : Measurable (fun p : ShortTime × HeatCircle ↦ point p.1 p.2) := by
  have hc (i : Fin 2) : Continuous (PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 i) := by
    apply Isometry.continuous
    intro x y
    simp only [PiLp.edist_single_same]
  exact (((hc 0).measurable.comp (measurable_subtype_coe.comp measurable_fst)).add
    ((hc 1).measurable.comp (measurable_representative.comp measurable_snd))).subtype_mk

theorem uniform_time_continuity (Y : Parameter → ℝ) (hY : Continuous Y)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      ∀ t s : ShortTime, |t.val - s.val| < δ → ∀ a : HeatCircle,
        |Y (point t a) - Y (point s a)| < ε := by
  obtain ⟨δ, hδ, hh⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hY) ε hε
  refine ⟨δ, hδ, fun t s hts a ↦ ?_⟩
  simpa only [Real.dist_eq] using hh ((point_distance t s a).trans_lt hts)

variable {Ω : Type*} [MeasurableSpace Ω]

def physical (Y : Parameter → Ω → ℝ) (t : ShortTime) (a : HeatCircle) (ω : Ω) : ℝ :=
  Y (point t a) ω

/-- Joint measurability of the pulled-back physical field follows from
the measurable continuous-path random variable and the measurable circle
representative, even across the representative's seam. -/
theorem measurable_physical (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω)) :
    Measurable (fun z : (ShortTime × HeatCircle) × Ω ↦ physical Y z.1.1 z.1.2 z.2) := by
  let Q (ω : Ω) : C(Parameter, ℝ) := ⟨fun p ↦ Y p ω, hc ω⟩
  have hQ : Measurable Q := ContinuousMap.measurable_iff_eval.mpr hm
  exact continuous_eval.measurable.comp
    ((hQ.comp measurable_snd).prodMk (measurable_point.comp measurable_fst))

end SHEStochastic.HeatParameterPullback
