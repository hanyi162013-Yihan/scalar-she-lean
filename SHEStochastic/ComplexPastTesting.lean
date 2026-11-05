module

public import SHEStochastic.BCFPastTesting
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.ComplexPastTesting
open MeasureTheory
open scoped NNReal ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → X) (hZ : Measurable Z)

include hZ in
/-- Existing real bounded-continuous density suffices for complex
characteristic martingales; no second monotone-class proof is needed. -/
theorem setIntegral_zero (Y : Ω → ℂ) (hY : MemLp Y 2 μ)
    (htest : ∀ f : BoundedContinuousFunction X ℝ, (∫ ω, f (Z ω) • Y ω ∂μ) = 0)
    {A : Set Ω} (hA : MeasurableSet[MeasurableSpace.comap Z inferInstance] A) :
    (∫ ω in A, Y ω ∂μ) = 0 := by
  have hparts := memLp_re_im_iff.mpr hY
  have hi (f : BoundedContinuousFunction X ℝ) : Integrable (fun ω ↦ f (Z ω) • Y ω) μ :=
    (hY.integrable one_le_two).bdd_smul ‖f‖
      (f.continuous.measurable.comp hZ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ f.norm_coe_le_norm _)
  have hre : (∫ ω in A, (Y ω).re ∂μ) = 0 := by
    apply BCFPastTesting.setIntegral_zero μ Z hZ _ hparts.1 _ hA
    intro f
    have hh := congrArg Complex.re (htest f)
    rw [← RCLike.re_eq_complex_re] at hh
    rw [← integral_re (hi f)] at hh
    simpa using hh
  have him : (∫ ω in A, (Y ω).im ∂μ) = 0 := by
    apply BCFPastTesting.setIntegral_zero μ Z hZ _ hparts.2 _ hA
    intro f
    have hh := congrArg Complex.im (htest f)
    rw [← RCLike.im_eq_complex_im] at hh
    rw [← integral_im (hi f)] at hh
    simpa using hh
  apply Complex.ext
  · simpa only [RCLike.re_eq_complex_re, Complex.zero_re] using
      (integral_re (hY.integrable one_le_two).integrableOn).symm.trans hre
  · simpa only [RCLike.im_eq_complex_im, Complex.zero_im] using
      (integral_im (hY.integrable one_le_two).integrableOn).symm.trans him

include hZ in
theorem condExp_zero (Y : Ω → ℂ) (hY : MemLp Y 2 μ)
    (htest : ∀ f : BoundedContinuousFunction X ℝ, (∫ ω, f (Z ω) • Y ω ∂μ) = 0) :
    μ[Y | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun _ ↦ (0 : ℂ) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hZ.comap_le (hY.integrable one_le_two)
    (fun _ _ _ ↦ (integrable_const (0 : ℂ)).integrableOn) (fun A hA _ ↦ ?_)
    stronglyMeasurable_zero.aestronglyMeasurable).symm
  rw [integral_zero]
  exact (setIntegral_zero μ Z hZ Y hY htest hA).symm

/-- Complex martingale recognition reuses the same real test density
for the entire generating past variable. -/
theorem martingale {T : Type*} [Preorder T]
    (F : Filtration T ‹MeasurableSpace Ω›) (past : T → Ω → X)
    (hpast : ∀ t, Measurable (past t))
    (hF : ∀ t, F t ≤ MeasurableSpace.comap (past t) inferInstance)
    (M : T → Ω → ℂ) (ha : StronglyAdapted F M) (hM : ∀ t, MemLp (M t) 2 μ)
    (htest : ∀ s t, s ≤ t → ∀ f : BoundedContinuousFunction X ℝ,
      (∫ ω, f (past s ω) • (M t ω-M s ω) ∂μ) = 0) :
    Martingale M F μ := by
  refine ⟨ha, fun s t hst ↦ ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) ((hM t).integrable one_le_two)
    (fun _ _ _ ↦ ((hM s).integrable one_le_two).integrableOn)
    (fun A hA _ ↦ ?_) (ha s).aestronglyMeasurable).symm
  have hz := setIntegral_zero μ (past s) (hpast s) (fun ω ↦ M t ω-M s ω)
    ((hM t).sub (hM s)) (htest s t hst) (hF s A hA)
  rw [integral_sub ((hM t).integrable one_le_two).integrableOn
    ((hM s).integrable one_le_two).integrableOn] at hz
  exact (sub_eq_zero.mp hz).symm

end SHEStochastic.ComplexPastTesting
