module

public import MathFin.Foundations.Esscher
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ConditionalMGF
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- A deterministic conditional MGF determines every past-restricted
law, including events of probability zero. This avoids conditioning on
individual values or normalizing event restrictions. -/
theorem restricted_law (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : @Measurable Ω ℝ mΩ _ X)
    (hν : ∀ a : ℝ, Integrable (fun x ↦ Real.exp (a * x)) ν)
    (hf : letI : MeasurableSpace Ω := mΩ
      ∀ a : ℝ, Integrable (fun ω ↦ Real.exp (a * X ω)) μ)
    (hc : letI : MeasurableSpace Ω := mΩ
      ∀ a : ℝ, μ[fun ω ↦ Real.exp (a * X ω) | m] =ᵐ[μ]
        (fun _ ↦ ∫ x, Real.exp (a * x) ∂ν))
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    letI : MeasurableSpace Ω := mΩ
    (μ.restrict A).map X = μ A • ν := by
  letI : MeasurableSpace Ω := mΩ
  haveI : IsFiniteMeasure (μ A • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact measure_lt_top μ A⟩
  apply Eq.symm
  apply MathFin.measure_eq_of_mgf_id_eq
    (fun a ↦ (hν a).smul_measure (measure_ne_top μ A))
  funext a
  change (∫ x, Real.exp (a * x) ∂μ A • ν) =
    ∫ x, Real.exp (a * x) ∂(μ.restrict A).map X
  rw [integral_smul_measure, integral_map hX.aemeasurable.restrict
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (a * x))
      ((μ.restrict A).map X))]
  calc
    _ = ∫ ω in A, (∫ x, Real.exp (a * x) ∂ν) ∂μ := (setIntegral_const _).symm
    _ = ∫ ω in A, μ[fun ω ↦ Real.exp (a * X ω) | m] ω ∂μ :=
      integral_congr_ae ((hc a).symm.filter_mono ae_restrict_le)
    _ = _ := setIntegral_condExp hm (hf a) hA

/-- The same conditional MGF identifies the law and proves independence
from the full given sigma algebra. -/
theorem law_and_independent (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : @Measurable Ω ℝ mΩ _ X)
    (hν : ∀ a : ℝ, Integrable (fun x ↦ Real.exp (a * x)) ν)
    (hf : letI : MeasurableSpace Ω := mΩ
      ∀ a : ℝ, Integrable (fun ω ↦ Real.exp (a * X ω)) μ)
    (hc : letI : MeasurableSpace Ω := mΩ
      ∀ a : ℝ, μ[fun ω ↦ Real.exp (a * X ω) | m] =ᵐ[μ]
        (fun _ ↦ ∫ x, Real.exp (a * x) ∂ν)) :
    letI : MeasurableSpace Ω := mΩ
    HasLaw X ν μ ∧ Indep (MeasurableSpace.comap X (borel ℝ)) m μ := by
  letI : MeasurableSpace Ω := mΩ
  have hlaw : μ.map X = ν := by
    simpa using restricted_law m hm hX hν hf hc (A := Set.univ) MeasurableSet.univ
  refine ⟨⟨hX.aemeasurable, hlaw⟩, (Indep_iff _ _ _).mpr ?_⟩
  intro B A hB hA
  obtain ⟨S, hS, rfl⟩ := hB
  have hres := congrArg (fun ρ : Measure ℝ ↦ ρ S)
    (restricted_law m hm hX hν hf hc hA)
  rw [Measure.map_apply hX hS, Measure.restrict_apply (hX hS),
    Measure.smul_apply, smul_eq_mul] at hres
  have hval : μ (X ⁻¹' S) = ν S := by
    rw [← hlaw, Measure.map_apply hX hS]
  rw [hval, mul_comm]
  exact hres

end SHEStochastic.ConditionalMGF
