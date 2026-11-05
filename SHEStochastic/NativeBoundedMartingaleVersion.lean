module

public import SHEStochastic.NativeBoundedMoments
public import SHEStochastic.FiniteCylindricalParameterVersions
public import SHEStochastic.DoobL2Envelope
public import SHEStochastic.ConditionalBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeBoundedMartingaleVersion
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Deterministic stopping beyond the horizon does not change an input. -/
theorem stop_cap (u : Process (E := C) F μ H) (t : ℝ≥0) :
    stop F μ H (min t H) u = stop F μ H t u := by
  calc
    _ = stop F μ H t (stop F μ H H u) := by
      simp only [StoppedInputAlgebra.stop_stop, NNReal.coe_min]
    _ = _ := by rw [FiniteItoStoppedVersions.stop_horizon]

/-- In a null-complete filtration the existing native continuous version
is predictable and a martingale. Bounded rows give every finite moment
through the already proved sub-Gaussian bound, independently of BDG. -/
theorem exists_version (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous (Y · ω)) ∧ StronglyAdapted F Y ∧
      StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧ Martingale Y F μ ∧
      (∀ t, Y t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u)) ∧
      (∀ t (p : ℝ≥0), MemLp (Y t) p μ) ∧
      (∀ t ω, Y t ω = Y (min t H) ω) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨U, hUc, hUr⟩ := FiniteCylindricalIto.continuousStoppedVersions P e u
  have hUa : StronglyAdapted F U := by
    apply NullCompleteFiltration.stronglyAdapted_of_versions F μ hnull
    intro t
    obtain ⟨Z, hZ, hrep⟩ := stopped_integral_adapted F μ H J t u
    have hh : U t =ᵐ[μ] J.integral (stop F μ H t u) := hUr t
    exact ⟨Z, hZ, hh.trans hrep⟩
  let Y (t : ℝ≥0) := U (min t H)
  have hYc (ω : Ω) : Continuous (Y · ω) :=
    (hUc ω).comp (continuous_id.min continuous_const)
  have hYa : StronglyAdapted F Y := fun t ↦ (hUa (min t H)).mono (F.mono (min_le_left t H))
  have hYp := ContinuousPredictable.stronglyMeasurable F Y hYa hYc
  have hYr (t : ℝ≥0) : Y t =ᵐ[μ] J.integral (stop F μ H t u) := by
    have hh := hUr (min t H)
    simp only [NNReal.coe_min] at hh
    rwa [stop_cap] at hh
  refine ⟨Y, hYc, hYa, hYp, ConditionalBracket.martingale J
    (FiniteCylindricalIto.pastLocality P e) u hYa hYr, hYr, ?_, ?_⟩
  · intro t p
    exact (memLp_congr_ae (hYr t)).mpr (NativeBoundedMoments.memLp_stopped P e u M hu t p)
  · intro t ω
    simp only [Y, min_assoc, min_self]

end SHEStochastic.NativeBoundedMartingaleVersion
