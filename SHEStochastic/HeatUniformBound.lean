module

public import SHE.BoundedHeat
public import SHE.RealHeat
public import SHEStochastic.L2ExtendedUniformNorm

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HeatUniformBound
open MeasureTheory SHE SHE.CircleHeat SHE.FiniteHaar SHE.DyadicApproximation AddCircle Set
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The actual normalized periodic heat kernel preserves an essential
uniform bound, without requiring a continuous initial representative. -/
theorem convolution_bound {t : ℝ} (ht : 0 < t) (f : CircleL2) (M : ℝ)
    (hf : ∀ᵐ y ∂haarAddCircle, ‖f y‖ ≤ M) (x : AddCircle (1 : ℝ)) :
    ‖∫ y : AddCircle (1 : ℝ), HeatMarkov.kernel t ht (y - x) * f y ∂haarAddCircle‖ ≤ M := by
  exact BoundedHeat.norm_bound ht f hf x

theorem heat_ae_bound {t : ℝ} (ht : 0 < t) (f : CircleL2) (M : ℝ)
    (hf : ∀ᵐ x ∂haarAddCircle, ‖f x‖ ≤ M) :
    ∀ᵐ x ∂haarAddCircle, ‖heat t f x‖ ≤ M := by
  filter_upwards [HeatMarkov.heat_convolution_ae ht f] with x hx
  rw [hx]
  exact convolution_bound ht f M hf x

theorem realHeat_ae_bound {t : ℝ} (ht : 0 ≤ t) (f : RealL2) (M : ℝ)
    (hf : ∀ᵐ x ∂haarAddCircle, ‖f x‖ ≤ M) :
    ∀ᵐ x ∂haarAddCircle, ‖RealHeat.realHeat t f x‖ ≤ M := by
  rcases ht.eq_or_lt with ht0 | htpos
  · subst t
    simpa only [RealHeat.realHeat_zero, ContinuousLinearMap.id_apply] using hf
  · have he : ∀ᵐ x ∂haarAddCircle, ‖realEmbed f x‖ ≤ M := by
      filter_upwards [realEmbed_ae f, hf] with x hx hfω
      simpa only [hx, Complex.norm_real, Real.norm_eq_abs] using hfω
    have hh := heat_ae_bound htpos (realEmbed f) M he
    rw [← RealHeat.realEmbed_realHeat] at hh
    filter_upwards [hh, realEmbed_ae (RealHeat.realHeat t f)] with x hx he
    simpa only [he, Complex.norm_real, Real.norm_eq_abs] using hx

end SHEStochastic.HeatUniformBound
