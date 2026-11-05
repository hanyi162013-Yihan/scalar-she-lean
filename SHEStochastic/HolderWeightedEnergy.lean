module

public import SHEStochastic.WeightedSublinearEnergy
public import SHEStochastic.UnboundedCoefficientCutoff
public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HolderWeightedEnergy
open MeasureTheory SHE.PredictableL2
open scoped NNReal ENNReal

variable {X E V : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup V]
  {ν : Measure X} {G : E → V} {C β : ℝ≥0}

theorem growth (hG : HolderWith C β G) (u : Lp E 2 ν) (x : X) :
    ENNReal.ofReal (‖G (u x)‖ ^ 2) ≤ ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2) *
      (1 + ENNReal.ofReal (‖u x‖ ^ 2) ^ (β : ℝ)) := by
  have he : ENNReal.ofReal (‖u x‖ ^ 2) ^ (β : ℝ) =
      ENNReal.ofReal (‖u x‖ ^ (2 * (β : ℝ))) := by
    calc
      _ = ENNReal.ofReal ((‖u x‖ ^ 2) ^ (β : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg ‖u x‖) β.property
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        norm_num
  have hh := ENNReal.ofReal_le_ofReal (UnboundedCoefficientCutoff.squared_growth hG (u x))
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
    (Real.rpow_nonneg (norm_nonneg _) _), ENNReal.ofReal_one, ← he] at hh
  exact hh

theorem state_mass (u : Lp E 2 ν) :
    (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂ν) = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Lp.memLp u).norm.integrable_sq
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _), ← realLp_norm_sq u]

/-- A single coefficient estimate for all kernel increments. The cap L
and unweighted energy Q can come from existing heat-semigroup estimates. -/
theorem bound (hG : HolderWith C β G) (hβ1 : β ≤ 1) (u : Lp E 2 ν)
    (h : X → ℝ≥0∞) (hh : AEMeasurable h ν) (L Q : ℝ≥0∞)
    (hcap : ∀ᵐ x ∂ν, h x ≤ L) (henergy : (∫⁻ x, h x ∂ν) ≤ Q) :
    (∫⁻ x, h x * ENNReal.ofReal (‖G (u x)‖ ^ 2) ∂ν) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2) *
        (Q + L ^ (β : ℝ) * (Q ^ (1 - (β : ℝ)) * ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ))) := by
  have hf : AEMeasurable (fun x ↦ ENNReal.ofReal (‖u x‖ ^ 2)) ν :=
    ((Lp.stronglyMeasurable u).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  have ht := WeightedSublinearEnergy.energy_with_growth ν h
    (fun x ↦ ENNReal.ofReal (‖u x‖ ^ 2)) (fun x ↦ ENNReal.ofReal (‖G (u x)‖ ^ 2)) hh hf
    (ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2)) L Q hcap henergy
    β.property (by exact_mod_cast hβ1) (Filter.Eventually.of_forall (growth hG u))
  rwa [state_mass u] at ht

end SHEStochastic.HolderWeightedEnergy
