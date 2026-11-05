module

public import SHEStochastic.HeatParameterPullback

import all Mathlib.Analysis.RCLike.Basic
import all Mathlib.Basic.Real.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GlobalHeatParameter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback SHE.StoppedFourier
open scoped NNReal ENNReal

/-- Cover the full finite time interval by scaling the existing compact
unit parameter domain. Spatial coordinates and their cover are reused. -/
def time (H : ℝ≥0) (p : Parameter) : ℝ≥0 := H*HeatParameterCoordinates.time 1 p

theorem time_le_horizon (H : ℝ≥0) (p : Parameter) : time H p≤H := by
  have hp : HeatParameterCoordinates.time 1 p≤1 := by exact_mod_cast time_le_one 1 p
  exact (mul_le_mul_of_nonneg_left hp H.property).trans_eq (mul_one H)

theorem time_lipschitz (H : ℝ≥0) : LipschitzWith H (time H) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hh := (HeatParameterCoordinates.time_lipschitz 1).dist_le_mul p q
  simp only [NNReal.coe_one, one_mul, NNReal.dist_eq] at hh
  change |(H:ℝ)*(HeatParameterCoordinates.time 1 p:ℝ)-(H:ℝ)*(HeatParameterCoordinates.time 1 q:ℝ)|≤(H:ℝ)*dist p q
  rw [← mul_sub, abs_mul]
  calc
    _ = (H:ℝ)*|(HeatParameterCoordinates.time 1 p:ℝ)-(HeatParameterCoordinates.time 1 q:ℝ)| := by
      congr 1
      exact abs_of_nonneg H.property
    _ ≤ _ := mul_le_mul_of_nonneg_left hh H.property

theorem zeroTime_time (H : ℝ≥0) (p : Parameter) : time H (zeroTime p)=0 := by
  rw [time, HeatParameterCoordinates.zeroTime_time, mul_zero]

def normalized (H : ℝ≥0) (hH : 0<H) (t : Set.Icc (0:ℝ) (H:ℝ)) : ShortTime :=
  ⟨t.val/(H:ℝ), div_nonneg t.property.1 H.property,
    (div_le_one (show 0<(H:ℝ) from hH)).mpr t.property.2⟩

theorem continuous_normalized (H : ℝ≥0) (hH : 0<H) : Continuous (normalized H hH) :=
  (continuous_subtype_val.div_const _).subtype_mk _

def point (H : ℝ≥0) (hH : 0<H) (t : Set.Icc (0:ℝ) (H:ℝ)) (a : HeatCircle) : Parameter :=
  HeatParameterPullback.point (normalized H hH t) a

theorem time_point (H : ℝ≥0) (hH : 0<H) (t : Set.Icc (0:ℝ) (H:ℝ)) (a : HeatCircle) :
    (time H (point H hH t a):ℝ)=t.val := by
  change (H:ℝ)*(HeatParameterCoordinates.time 1 (HeatParameterPullback.point (normalized H hH t) a):ℝ)=_
  have he := HeatParameterPullback.time_point 1 (normalized H hH t) a (normalized H hH t).property.2
  calc
    _ = (H:ℝ)*(normalized H hH t).val := by
      convert! congrArg (fun z : ℝ ↦ (H:ℝ)*z) he using 1
    _ = _ := by
      dsimp only [normalized]
      field_simp [show (H:ℝ)≠0 from ne_of_gt hH]

end SHEStochastic.GlobalHeatParameter
