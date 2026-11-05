module

public import SHE.SmoothCylinderAlgebra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.SmoothTestLaw
open MeasureTheory ProbabilityTheory SmoothCylinders

theorem boundedSmooth_cos : BoundedSmooth Real.cos := by
  refine ⟨Real.contDiff_cos,fun k => ⟨1,fun x => ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs] using
    Real.abs_iteratedDeriv_cos_le_one k x

theorem boundedSmooth_sin : BoundedSmooth Real.sin := by
  refine ⟨Real.contDiff_sin,fun k => ⟨1,fun x => ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs] using
    Real.abs_iteratedDeriv_sin_le_one k x

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Genuine all-order bounded smooth real tests determine a finite
Hilbert-space law. The proof uses explicit cosine/sine linear tests and
uniqueness of characteristic functions, not an extra probability input. -/
theorem measure_eq (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (htest : ∀ (F : E → ℝ), BoundedSmooth F → (∫ x,F x ∂μ)=(∫ x,F x ∂ν)) : μ=ν := by
  apply Measure.ext_of_charFun
  funext t
  have hi (m : Measure E) [IsFiniteMeasure m] :
      Integrable (fun x => Complex.exp ((inner ℝ x t : ℝ)*Complex.I)) m := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simp)
  have hc := htest (fun x => Real.cos (innerSL ℝ t x))
    (boundedSmooth_cos.comp_right (innerSL ℝ t))
  have hs := htest (fun x => Real.sin (innerSL ℝ t x))
    (boundedSmooth_sin.comp_right (innerSL ℝ t))
  apply Complex.ext
  · change RCLike.re (∫ x,Complex.exp ((inner ℝ x t : ℝ)*Complex.I) ∂μ)=
      RCLike.re (∫ x,Complex.exp ((inner ℝ x t : ℝ)*Complex.I) ∂ν)
    rw [←integral_re (hi μ),←integral_re (hi ν)]
    change (∫ x,(Complex.exp ((inner ℝ x t : ℝ)*Complex.I)).re ∂μ)=
      ∫ x,(Complex.exp ((inner ℝ x t : ℝ)*Complex.I)).re ∂ν
    simpa only [Complex.exp_ofReal_mul_I_re,innerSL_apply_apply,real_inner_comm] using hc
  · change RCLike.im (∫ x,Complex.exp ((inner ℝ x t : ℝ)*Complex.I) ∂μ)=
      RCLike.im (∫ x,Complex.exp ((inner ℝ x t : ℝ)*Complex.I) ∂ν)
    rw [←integral_im (hi μ),←integral_im (hi ν)]
    change (∫ x,(Complex.exp ((inner ℝ x t : ℝ)*Complex.I)).im ∂μ)=
      ∫ x,(Complex.exp ((inner ℝ x t : ℝ)*Complex.I)).im ∂ν
    simpa only [Complex.exp_ofReal_mul_I_im,innerSL_apply_apply,real_inner_comm] using hs

/-- A transition identity on all bounded smooth tests certifies the
actual pushforward distribution, including singular Gaussian laws. -/
theorem hasLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → E) (hX : Measurable X) (ν : Measure E) [IsFiniteMeasure ν]
    (htest : ∀ (F : E → ℝ), BoundedSmooth F →
      (∫ ω,F (X ω) ∂μ)=(∫ x,F x ∂ν)) : HasLaw X ν μ := by
  refine ⟨hX.aemeasurable,measure_eq (μ.map X) ν ?_⟩
  intro F hF
  rw [integral_map hX.aemeasurable hF.smooth.continuous.measurable.aestronglyMeasurable]
  exact htest F hF

end SHE.SmoothTestLaw
