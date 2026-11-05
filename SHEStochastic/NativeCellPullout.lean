module

public import SHEStochastic.NativeRowRepresentatives
public import SHEStochastic.FiniteCylindricalLocality
public import SHE.BoundedPastItoMultiplier
public import SHE.PredictableSteps

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeCellPullout
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

theorem bounded_memLp {s : ℝ≥0} {R : Ω → C} (hR : StronglyMeasurable[F s] R)
    (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) : MemLp R 2 μ :=
  MemLp.of_bound (hR.mono (F.le s)).aestronglyMeasurable K (Filter.Eventually.of_forall hK)

def process (s t : ℝ≥0) (R : Ω → C) (hR : StronglyMeasurable[F s] R)
    (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) : Process (E := C) F μ H :=
  PredictableSteps.process F μ H s t R hR (bounded_memLp hR K hK)

theorem process_ae (s t : ℝ≥0) (R : Ω → C) (hR : StronglyMeasurable[F s] R)
    (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) :
    process (μ := μ) (H := H) s t R hR K hK =ᵐ[energyMeasure μ H] PredictableSteps.step s t R :=
  PredictableSteps.process_ae F μ H s t R hR (bounded_memLp hR K hK)

theorem transport_process (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    FiniteCylindricalIto.processTransport (process s t R hR K hK) =
      HilbertSimpleInputs.embedding F μ H (HilbertSimpleInputs.step s t hst htH R hR K hK) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  have ht := NativeRowRepresentatives.transport_ae (μ := μ) (H := H) (process s t R hR K hK)
    (PredictableSteps.step s t R) (PredictableSteps.step_stronglyMeasurable F s t hR)
    (process_ae s t R hR K hK)
  filter_upwards [ht, HilbertSimpleInputs.embedding_ae F μ H
    (HilbertSimpleInputs.step s t hst htH R hR K hK)] with p hp hq
  rw [hp, hq]
  change PredictableSteps.step s t R p = (HilbertSimpleInputs.step s t hst htH R hR K hK).val p.1 p.2
  simp [PredictableSteps.step, HilbertSimpleInputs.step_apply, Set.indicator_apply]

/-- Reuse of the already verified bounded past-multiplier theorem for
the actual native Hilbert cell integral. -/
theorem pullout (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K)
    (f : Ω → ℝ) (hf : StronglyMeasurable[F s] f) (M : ℝ) (hM : 0 ≤ M) (hfb : ∀ ω, |f ω| ≤ M)
    (hprod : ∀ ω, ‖f ω • R ω‖ ≤ M * K) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H
      (HilbertSimpleInputs.step s t hst htH (fun ω ↦ f ω • R ω) (hf.smul hR) (M * K) hprod)) =ᵐ[μ]
    (fun ω ↦ f ω * FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H
      (HilbertSimpleInputs.step s t hst htH R hR K hK)) ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let u := process (μ := μ) (H := H) s t R hR K hK
  let uf := process (μ := μ) (H := H) s t (fun ω ↦ f ω • R ω) (hf.smul hR) (M * K) hprod
  obtain ⟨v, hv, hJv⟩ := BoundedPastItoMultiplier.exists_input F μ H s J
    (FiniteCylindricalIto.pastLocality P e) u f hf M hM hfb
  have hpost : post F μ H s u = u := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [post_ae F μ H s u, process_ae s t R hR K hK] with p hp hu
    rw [hp, hu]
    by_cases hm : p.1 ∈ Set.Ioc s t
    · simp [PredictableSteps.step, hm, hm.1]
    · simp [PredictableSteps.step, hm]
  have hvf : v = uf := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [hv, process_ae s t R hR K hK,
      process_ae s t (fun ω ↦ f ω • R ω) (hf.smul hR) (M * K) hprod] with p hp hu huf
    rw [hp, hu, huf]
    by_cases hm : p.1 ∈ Set.Ioc s t
    · simp [PredictableSteps.step, hm, hm.1]
    · simp [PredictableSteps.step, hm]
  rw [hvf, hpost] at hJv
  have hI : J.integral u = FiniteCylindricalIto.rawIntegral P.toCoordinates e
      (HilbertSimpleInputs.embedding F μ H (HilbertSimpleInputs.step s t hst htH R hR K hK)) := by
    change FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.processTransport u) = _
    rw [transport_process s t hst htH R hR K hK]
  have hIf : J.integral uf = FiniteCylindricalIto.rawIntegral P.toCoordinates e
      (HilbertSimpleInputs.embedding F μ H (HilbertSimpleInputs.step s t hst htH
        (fun ω ↦ f ω • R ω) (hf.smul hR) (M * K) hprod)) := by
    change FiniteCylindricalIto.rawIntegral P.toCoordinates e (FiniteCylindricalIto.processTransport uf) = _
    rw [transport_process s t hst htH (fun ω ↦ f ω • R ω) (hf.smul hR) (M * K) hprod]
  rwa [hI, hIf] at hJv

end SHEStochastic.NativeCellPullout
