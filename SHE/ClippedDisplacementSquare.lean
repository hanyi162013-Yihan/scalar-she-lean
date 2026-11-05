module

public import SHE.PolynomialGaussianDecay

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.ClippedDisplacementSquare
open Set MeasureTheory Real
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- A physical state displacement may be correlated with everything
else. Its clipped square averages to the minimum of one and its actual
L² energy at the band scale. -/
theorem integral_clip {d : X→ℝ} (hd : Measurable d) (hi : Integrable (fun x=>d x^2) ν)
    {r : ℝ} (hr : 0<r) :
    Integrable (fun x=>(min 1 (|d x|/r))^2) ν ∧
    (∫ x,(min 1 (|d x|/r))^2 ∂ν)≤min 1 ((∫ x,d x^2 ∂ν)/r^2) := by
  have hm : Measurable (fun x=>(min 1 (|d x|/r))^2):=by
    have ha:=continuous_abs.measurable.comp hd
    exact ((measurable_const.min (ha.div_const r)).pow_const 2)
  have hnon (x : X) : 0≤min 1 (|d x|/r):=le_min zero_le_one (div_nonneg (abs_nonneg _) hr.le)
  have hpoint (x : X) : (min 1 (|d x|/r))^2≤1:=
    (pow_le_pow_left₀ (hnon x) (min_le_left _ _) 2).trans_eq (by norm_num)
  have hI : Integrable (fun x=>(min 1 (|d x|/r))^2) ν:=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ (fun x=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint x))
  refine ⟨hI,le_min ?_ ?_⟩
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hI (integrable_const (1:ℝ)) hpoint
  · have hdom (x : X) : (min 1 (|d x|/r))^2≤d x^2/r^2:=by
      have hh:=pow_le_pow_left₀ (hnon x) (min_le_right 1 (|d x|/r)) 2
      simpa only [div_pow,sq_abs] using hh
    simpa only [integral_div] using integral_mono hI (hi.div_const (r^2)) hdom

end SHE.ClippedDisplacementSquare
