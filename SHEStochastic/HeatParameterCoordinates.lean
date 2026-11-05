module

public import SHEStochastic.HeatParameterCover
public import SHE.NativeHeatSpan
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.HeatParameterCoordinates
open HeatParameterCover SHE SHE.StoppedFourier SHE.NativeHeatSpan
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def time (H : ℝ≥0) (p : Parameter) : ℝ≥0 :=
  ⟨min (max (p.val 0) 0) (min (H : ℝ) 1),
    le_min (le_max_right _ _) (le_min H.property zero_le_one)⟩

theorem time_le_horizon (H : ℝ≥0) (p : Parameter) : time H p ≤ H :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem time_le_one (H : ℝ≥0) (p : Parameter) : (time H p : ℝ) ≤ 1 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem coordinate_lipschitz (i : Fin 2) : LipschitzWith 1 (fun p : Parameter ↦ p.val i) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul]
  convert PiLp.dist_apply_le p.val q.val i using 1 <;> rfl

theorem time_lipschitz (H : ℝ≥0) : LipschitzWith 1 (time H) := by
  have hh := ((coordinate_lipschitz 0).max_const 0).min_const (min (H : ℝ) 1)
  exact hh.subtype_mk (fun p ↦ le_min (le_max_right _ _) (le_min H.property zero_le_one))

def center (p : Parameter) : HeatCircle :=
  CircleNormalization.scale 1 (2 * Real.pi) ((p.val 1 : ℝ) : UnitAddCircle)

theorem unit_center (p : Parameter) : unitCenter (center p) = ((p.val 1 : ℝ) : UnitAddCircle) := by
  simp only [center, unitCenter, CircleNormalization.scale, AddCircle.equivAddCircle_apply_mk]
  congr 1
  field_simp

theorem spatial_distance_le (p q : Parameter) :
    ‖unitCenter (center p) - unitCenter (center q)‖ ≤ dist p q := by
  rw [unit_center, unit_center, ← QuotientAddGroup.mk_sub]
  exact QuotientAddGroup.norm_mk_le_norm.trans (by
    have hh := PiLp.dist_apply_le p.val q.val 1
    simp only [dist_eq_norm] at hh
    convert hh using 1 <;> rfl)

/-- Project a parameter onto the initial-time line, retaining its
spatial coordinate. The projection stays inside the same compact ball. -/
def zeroTime (p : Parameter) : Parameter :=
  ⟨PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 1 (p.val 1), by
    have hp := p.property
    change p.val ∈ Metric.closedEBall (0 : Plane) (2 : ℝ≥0) at hp
    rw [Metric.closedEBall_coe, Metric.mem_closedBall, dist_zero_right] at hp
    change (PiLp.single 2 1 (p.val 1) : Plane) ∈ Metric.closedEBall (0 : Plane) (2 : ℝ≥0)
    rw [Metric.closedEBall_coe, Metric.mem_closedBall, dist_zero_right, PiLp.norm_single]
    exact (PiLp.norm_apply_le p.val 1).trans hp⟩

theorem continuous_zeroTime : Continuous zeroTime := by
  have hi : Isometry (PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 1) := by
    intro x y
    simp only [PiLp.edist_single_same]
  exact (hi.continuous.comp (coordinate_lipschitz 1).continuous).subtype_mk _

theorem zeroTime_time (H : ℝ≥0) (p : Parameter) : time H (zeroTime p) = 0 := by
  apply Subtype.ext
  simp [time, zeroTime] <;> rfl

theorem zeroTime_center (p : Parameter) : center (zeroTime p) = center p := by
  simp only [center, zeroTime, PiLp.single_eq_same]

theorem zeroTime_distance (p : Parameter) : dist p (zeroTime p) = |p.val 0| := by
  have hv : p.val - (zeroTime p).val = PiLp.single 2 0 (p.val 0) := by
    ext i
    fin_cases i <;> simp [zeroTime]
  change ‖p.val - (zeroTime p).val‖ = |p.val 0|
  rw [hv, PiLp.norm_single, Real.norm_eq_abs]

end SHEStochastic.HeatParameterCoordinates
