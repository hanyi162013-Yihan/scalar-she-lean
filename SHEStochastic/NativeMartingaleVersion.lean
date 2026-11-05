module

public import SHEStochastic.FiniteCylindricalParameterVersions
public import SHEStochastic.FiniteCylindricalLocality
public import SHEStochastic.ConditionalBracket
public import SHE.ContinuousPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeMartingaleVersion
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Every native predictable L2 input has one adapted continuous
martingale version. No pointwise bound on the input is required. -/
theorem exists_version (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (u : Process (E := C) F μ H) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous (Y · ω)) ∧ StronglyAdapted F Y ∧
      StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧ Martingale Y F μ ∧
      ∀ t, Y t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨Y, hc, hr⟩ := FiniteCylindricalIto.continuousStoppedVersions P e u
  have ha : StronglyAdapted F Y := by
    apply NullCompleteFiltration.stronglyAdapted_of_versions F μ hnull
    intro t
    obtain ⟨Z, hZ, he⟩ := stopped_integral_adapted F μ H J t u
    have ht : Y t =ᵐ[μ] (J.integral (stop F μ H t u) : Ω → ℝ) := hr t
    exact ⟨Z, hZ, ht.trans he⟩
  exact ⟨Y, hc, ha, ContinuousPredictable.stronglyMeasurable F Y ha hc,
    ConditionalBracket.martingale J (FiniteCylindricalIto.pastLocality P e) u ha hr, hr⟩

end SHEStochastic.NativeMartingaleVersion
