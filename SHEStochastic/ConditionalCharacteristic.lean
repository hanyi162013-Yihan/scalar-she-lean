module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ConditionalCharacteristic
open MeasureTheory ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure E} [IsProbabilityMeasure ν]

/-- Event-tested characteristic functions determine every restricted
law directly, including null events. No conditional probability kernel
or normalization of a restricted measure is needed. -/
theorem restricted_law (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X : Ω → E} (hX : @Measurable Ω E mΩ _ X)
    (htest : letI : MeasurableSpace Ω := mΩ
      ∀ x : E, ∀ A : Set Ω, MeasurableSet[m] A →
        (∫ ω in A, Complex.exp ((inner ℝ (X ω) x : ℂ) * Complex.I) ∂μ) =
          μ.real A • charFun ν x)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    letI : MeasurableSpace Ω := mΩ
    (μ.restrict A).map X = μ A • ν := by
  letI : MeasurableSpace Ω := mΩ
  haveI : IsFiniteMeasure (μ A • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact measure_lt_top μ A⟩
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_apply, charFun_apply, integral_map hX.aemeasurable.restrict
    (by fun_prop : AEStronglyMeasurable
      (fun y : E ↦ Complex.exp ((inner ℝ y x : ℂ) * Complex.I)) ((μ.restrict A).map X)),
    integral_smul_measure]
  exact htest x A hA

/-- Identification of the vector law together with independence from
the entire supplied past sigma algebra. -/
theorem law_and_independent (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X : Ω → E} (hX : @Measurable Ω E mΩ _ X)
    (htest : letI : MeasurableSpace Ω := mΩ
      ∀ x : E, ∀ A : Set Ω, MeasurableSet[m] A →
        (∫ ω in A, Complex.exp ((inner ℝ (X ω) x : ℂ) * Complex.I) ∂μ) =
          μ.real A • charFun ν x) :
    letI : MeasurableSpace Ω := mΩ
    HasLaw X ν μ ∧ Indep (MeasurableSpace.comap X (borel E)) m μ := by
  letI : MeasurableSpace Ω := mΩ
  have hlaw : μ.map X = ν := by
    simpa using restricted_law m hm hX htest (A := Set.univ) MeasurableSet.univ
  refine ⟨⟨hX.aemeasurable, hlaw⟩, (Indep_iff _ _ _).mpr ?_⟩
  intro B A hB hA
  obtain ⟨S, hS, rfl⟩ := hB
  rw [← BorelSpace.measurable_eq (α := E)] at hS
  have hres := congrArg (fun ρ : Measure E ↦ ρ S) (restricted_law m hm hX htest hA)
  rw [Measure.map_apply hX hS, Measure.restrict_apply (hX hS),
    Measure.smul_apply, smul_eq_mul] at hres
  have hval : μ (X ⁻¹' S) = ν S := by rw [← hlaw, Measure.map_apply hX hS]
  rw [hval, mul_comm]
  exact hres

/-- Independence from a sigma algebra is unchanged by replacing the
random vector with an almost-everywhere equal version. -/
theorem indep_comap_congr (m : MeasurableSpace Ω) {X Y : Ω → E}
    (hYX : Y =ᵐ[μ] X) (hi : Indep (MeasurableSpace.comap X (borel E)) m μ) :
    Indep (MeasurableSpace.comap Y (borel E)) m μ := by
  apply (Indep_iff _ _ _).mpr
  intro B A hB hA
  obtain ⟨S, hS, rfl⟩ := hB
  have he : Y ⁻¹' S =ᵐ[μ] X ⁻¹' S := by
    filter_upwards [hYX] with ω hω
    simp only [Set.mem_preimage, hω]
  have hei : Y ⁻¹' S ∩ A =ᵐ[μ] X ⁻¹' S ∩ A := he.inter Filter.EventuallyEqSet.rfl
  rw [measure_congr hei, measure_congr he]
  exact (Indep_iff _ _ _).mp hi _ A ⟨S, hS, rfl⟩ hA

end SHEStochastic.ConditionalCharacteristic
