module

public import SHEStochastic.HilbertSimpleInputs
public import SHEStochastic.BrownianGaussianStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertSimpleIntegral
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- Hilbert-valued simple rows retain the original coordinate integrals.
Their scalar coordinate sum converges in the original terminal L2 space. -/
theorem hasSum (P : FiniteScalarIto.Coordinates F μ H ι) (e : HilbertBasis ι ℝ C)
    (V : HilbertSimpleInputs.bounded (E := C) F H) :
    HasSum (fun i ↦ FiniteScalarIto.simpleLp P i (HilbertSimpleInputs.map (innerSL ℝ (e i)) V))
      (FiniteCylindricalIto.rawIntegral P e (HilbertSimpleInputs.embedding F μ H V)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hc (i : ι) :
      FiniteCylindricalIto.sourceEquiv e (HilbertSimpleInputs.embedding F μ H V) i =
        FiniteScalarIto.embedding F μ H (HilbertSimpleInputs.map (innerSL ℝ (e i)) V) := by
    rw [FiniteCylindricalIto.sourceEquiv_coordinate, ← HilbertSimpleInputs.embedding_map,
      HilbertSimpleInputs.embedding_scalar]
  simpa only [hc, FiniteScalarIto.rawIsometry_simple] using
    FiniteCylindricalIto.rawIntegral_hasSum P e (HilbertSimpleInputs.embedding F μ H V)

/-- A scalar coordinate of a frozen Hilbert row integrates to the
literal original-coordinate increment with its left-past coefficient. -/
theorem mapped_step_value (P : FiniteScalarIto.Coordinates F μ H ι) (i : ι)
    (L : C →L[ℝ] ℝ) (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) :
    FiniteScalarIto.simpleValue P i
      (HilbertSimpleInputs.map L (HilbertSimpleInputs.step s t hst htH R hR K hK)) =
      (fun ω ↦ L (R ω) * (P.W i t ω - P.W i s ω)) := by
  funext ω
  simp [FiniteScalarIto.simpleValue, FilteredItoL2.itoSimple, HilbertSimpleInputs.map,
    SimpleProcessLinearMap.map, HilbertSimpleInputs.step, Finsupp.mapRange_single]

theorem mapped_step_ae (P : FiniteScalarIto.Coordinates F μ H ι) (i : ι)
    (L : C →L[ℝ] ℝ) (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) :
    FiniteScalarIto.simpleLp P i
      (HilbertSimpleInputs.map L (HilbertSimpleInputs.step s t hst htH R hR K hK)) =ᵐ[μ]
      (fun ω ↦ L (R ω) * (P.W i t ω - P.W i s ω)) := by
  have hh := (FiniteScalarIto.memLp_simpleValue P i
    (HilbertSimpleInputs.map L (HilbertSimpleInputs.step s t hst htH R hR K hK))).coeFn_toLp
  filter_upwards [hh] with ω hω
  exact hω.trans (congrFun (mapped_step_value P i L s t hst htH R hR K hK) ω)

end SHEStochastic.HilbertSimpleIntegral
