module

public import SHEStochastic.NativeMartingaleVersion
public import SHEStochastic.NativeBrownianCoordinates
public import BrownianMotion.Continuity.KolmogorovChentsov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.NativeBrownianVersion
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- The constant-row native integral equals the given Brownian coordinate
simultaneously throughout the closed integration horizon. -/
theorem exists_version (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (i : ι) :
    ∃ N : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (N · ω)) ∧ StronglyAdapted F N ∧
      (∀ t, N t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H t (RotatedCylindricalCoordinates.constant F μ H (e i)))) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ H → N t ω = P.W i t ω := by
  obtain ⟨N, hcN, haN, _, _, hrN⟩ := NativeMartingaleVersion.exists_version P e hnull
    (RotatedCylindricalCoordinates.constant F μ H (e i))
  refine ⟨N, hcN, haN, hrN, ?_⟩
  have hh := indistinguishable_of_edist_modification
    (Filter.Eventually.of_forall fun ω ↦ (hcN ω).comp (continuous_id.min (continuous_const (y := H))))
    (Filter.Eventually.of_forall fun ω ↦ (P.continuous i ω).comp (continuous_id.min (continuous_const (y := H))))
    (fun t ↦ ((hrN (min t H)).trans
      (FiniteCylindricalIto.coordinate_integral P e i (min t H) (min_le_right _ _))).mono
        fun ω hω ↦ by
          change edist (N (min t H) ω) (P.W i (min t H) ω) = 0
          rw [hω, edist_self])
  filter_upwards [hh] with ω hω t ht
  simpa only [Function.comp_apply, id_eq, min_eq_left ht] using edist_eq_zero.mp (hω t)

end SHEStochastic.NativeBrownianVersion
