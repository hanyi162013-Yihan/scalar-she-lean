module

public import SHEStochastic.NativeRotatedFamily
public import SHEStochastic.NativeIntegralUniqueness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativePredictableRotation
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω A C ι κ : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) (b : HilbertBasis κ ℝ A)
  (Φ : ℝ≥0 × Ω → A →ₗᵢ[ℝ] C)
  (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
    (F.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p ↦ Φ p.1 p.2))

/-- The actual Brownian family obtained by predictable rotation has
the transported native integral on every predictable L2 input. Thus all
native stochastic packages can be reused for this family directly. -/
theorem exists_family (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Q : FiniteScalarIto.Family F μ H κ, ∀ u : Process (E := A) F μ H,
      (FiniteCylindricalIto.terminalIto Q.toCoordinates b).integral u =
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (PredictableItoRotation.processIsometry F μ H Φ hΦ u) := by
  obtain ⟨Q, hQ⟩ := NativeRotatedFamily.exists_family P e b Φ hΦ hnull
  let J := PredictableItoRotation.integral F μ H Φ hΦ
    (FiniteCylindricalIto.terminalIto P.toCoordinates e)
  have hl : StandardTerminalPastLocality J :=
    PredictableRotationLocality.pastLocality F μ H Φ hΦ _ (FiniteCylindricalIto.pastLocality P e)
  have hc (i : κ) (t : ℝ≥0) (_ : t ≤ H) :
      RawCylindricalCoordinates.value F μ H (b : κ → A) J i t =ᵐ[μ] Q.W i t :=
    (hQ i t).symm
  refine ⟨Q, fun u ↦ ?_⟩
  exact (NativeIntegralUniqueness.integral Q b J hl hc u).symm

end SHEStochastic.NativePredictableRotation
