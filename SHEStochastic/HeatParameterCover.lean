module

public import BrownianMotion.Continuity.CoveringNumber
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.HeatParameterCover
open Metric Set
open scoped NNReal ENNReal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A compact two-dimensional parameter domain containing the unit
time-space square. Its subtype has an open full domain for Chentsov. -/
def region : Set Plane := closedEBall 0 2
abbrev Parameter := region

instance parameter_compact : CompactSpace Parameter := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact (closedEBall (0 : Plane) (2 : ℝ≥0))
  rw [closedEBall_coe]
  exact isCompact_closedBall _ _

theorem region_cover : HasCoveringExponent region 64 2 where
  ediam_lt_top := (ediam_closedEBall_le (x := (0 : Plane))).trans_lt (by norm_num)
  coveringNumber_le ε hε := by
    have hε4 : (ε : ℝ≥0∞) ≤ 4 := hε.trans (by
      exact (ediam_closedEBall_le (x := (0 : Plane)) (r := 2)).trans_eq (by norm_num))
    have hc := coveringNumber_closedBall_le ε (0 : Plane) (2 : ℝ≥0)
    have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
    simp only [hdim, ENNReal.coe_ofNat,
      show (2 : ℝ≥0∞) * 2 = 4 by norm_num] at hc
    change (coveringNumber ε region : ℝ≥0∞) ≤ _
    obtain rfl | hε0 := eq_zero_or_pos ε
    · simp
    have hlin : (4 : ℝ≥0∞) / ε + 1 ≤ 8 / ε := by
      have h1 : (1 : ℝ≥0∞) ≤ 4 / ε := by
        rw [ENNReal.le_div_iff_mul_le (.inl (by exact_mod_cast hε0.ne')) (.inr (by simp)), one_mul]
        exact hε4
      calc
        _ ≤ (4 : ℝ≥0∞) / ε + 4 / ε := add_le_add le_rfl h1
        _ = _ := by simp only [div_eq_mul_inv]; ring
    calc
      _ ≤ ((4 : ℝ≥0∞) / ε + 1) ^ 2 := hc
      _ ≤ ((8 : ℝ≥0∞) / ε) ^ 2 := by gcongr
      _ = (64 : ℝ≥0∞) * (ε : ℝ≥0∞)⁻¹ ^ (2 : ℝ) := by
        rw [ENNReal.rpow_two]
        simp only [div_eq_mul_inv]
        ring

theorem parameter_cover : HasCoveringExponent (Set.univ : Set Parameter) 64 2 := by
  have hi : Isometry (Subtype.val : Parameter → Plane) := isometry_subtype_coe
  have himage : (Subtype.val : Parameter → Plane) '' Set.univ = region := by
    simp
  refine ⟨?_, ?_⟩
  · rw [← hi.ediam_image, himage]
    exact region_cover.ediam_lt_top
  · intro ε hε
    rw [← hi.coveringNumber_image, himage]
    apply region_cover.coveringNumber_le
    rwa [← hi.ediam_image, himage] at hε

end SHEStochastic.HeatParameterCover
