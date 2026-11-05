module

public import SHEStochastic.NativeFourierHeatCoordinate

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.NativeFourierStateSeparation
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open NativeFourierHeatCoordinate

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- A countable family of real and imaginary Fourier coordinates
determines the original native real L2 state. -/
theorem ext {u v : RealL2}
    (hre : ∀ n : ℤ, coordinate Complex.reCLM n u = coordinate Complex.reCLM n v)
    (him : ∀ n : ℤ, coordinate Complex.imCLM n u = coordinate Complex.imCLM n v) : u = v := by
  have he : NativeHeatObservation.embed u = NativeHeatObservation.embed v := by
    apply (_root_.fourierBasis (T := 2 * Real.pi)).repr.injective
    apply lp.ext
    funext n
    rw [fourierBasis_repr, fourierBasis_repr]
    apply Complex.ext
    · simpa only [coordinate, ContinuousLinearMap.comp_apply,
        NativeMultiplierFourierIntegral.coefficient_apply, Complex.reCLM_apply] using hre n
    · simpa only [coordinate, ContinuousLinearMap.comp_apply,
        NativeMultiplierFourierIntegral.coefficient_apply, Complex.imCLM_apply] using him n
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← NativeHeatObservation.embed_norm, map_sub, he, sub_self, norm_zero]

end SHEStochastic.NativeFourierStateSeparation
