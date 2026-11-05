module

public import SHEStochastic.UnboundedCoefficientCutoff
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HolderCoefficientIntegrability
open MeasureTheory
open scoped NNReal ENNReal

variable {X E V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {ν : Measure X} [IsFiniteMeasure ν]

/-- The higher spatial integrability supplied by a Hölder coefficient:
an L² state gives an L^(2/β) coefficient field. This is the exponent
used with the squared heat kernel, including for matrix-valued G. -/
theorem memLp_comp {G : E → V} {C β : ℝ≥0} (hβ : 0 < β)
    (hG : HolderWith C β G) {u : X → E} (hu : MemLp u 2 ν) :
    MemLp (fun x ↦ G (u x)) (2 / (β : ℝ≥0∞)) ν := by
  have hp := hu.norm_rpow_div (β : ℝ≥0∞)
  simp only [ENNReal.coe_toReal] at hp
  have hd : MemLp (fun x ↦ ‖G 0‖ + (C : ℝ) * ‖u x‖ ^ (β : ℝ))
      (2 / (β : ℝ≥0∞)) ν :=
    (memLp_const ‖G 0‖).add (hp.const_mul (C : ℝ))
  apply hd.mono' ((hG.uniformContinuous hβ).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x ↦ UnboundedCoefficientCutoff.norm_le_origin_add hG (u x)

theorem memLp_two {G : E → V} {C β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hG : HolderWith C β G) {u : X → E} (hu : MemLp u 2 ν) :
    MemLp (fun x ↦ G (u x)) 2 ν := by
  apply (memLp_comp hβ hG hu).mono_exponent
  apply (ENNReal.le_div_iff_mul_le (Or.inr (by norm_num)) (Or.inl ENNReal.coe_ne_top)).mpr
  have hh : (β : ℝ≥0∞) ≤ 1 := by exact_mod_cast hβ1
  simpa only [mul_one] using mul_le_mul_right hh 2

/-- The actual L2 coefficient class of an L2 state, including
unbounded globally Holder coefficients with exponent at most one. -/
def coefficient {G : E → V} {C β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hG : HolderWith C β G) (u : Lp E 2 ν) : Lp V 2 ν :=
  (memLp_two hβ hβ1 hG (Lp.memLp u)).toLp _

theorem coefficient_ae {G : E → V} {C β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hG : HolderWith C β G) (u : Lp E 2 ν) :
    coefficient hβ hβ1 hG u =ᵐ[ν] fun x ↦ G (u x) :=
  (memLp_two hβ hβ1 hG (Lp.memLp u)).coeFn_toLp

/-- Every radial cutoff has the SAME higher spatial integrability
exponent, with the same Hölder constant. -/
theorem cutoff_memLp {G : E → V} {C β : ℝ≥0} (hβ : 0 < β)
    (hG : HolderWith C β G) {u : X → E} (hu : MemLp u 2 ν) (R : ℝ≥0) :
    MemLp (fun x ↦ UnboundedCoefficientCutoff.coefficient G R (u x)) (2 / (β : ℝ≥0∞)) ν :=
  memLp_comp hβ (UnboundedCoefficientCutoff.holder hG R) hu

end SHEStochastic.HolderCoefficientIntegrability
