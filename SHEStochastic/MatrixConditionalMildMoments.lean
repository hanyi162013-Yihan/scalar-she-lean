module

public import SHEStochastic.MatrixConditionalMildSolution
public import SHEStochastic.MatrixWeakStateEnergy
public import SHEStochastic.ConditionalKernelL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.MatrixConditionalMildMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar CanonicalStateDriverFiltration
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩

/-- Almost every continuation kernel has L2 states at every local
time. Its given initial state is deterministic under that kernel, so
this needs no additional conditional initial-moment hypothesis. -/
theorem state_memLp (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×HaarNode) H))
    [IsProbabilityMeasure Q] (G : MatrixNonlinearCoefficient.Coefficient d) (hH : (H : ℝ)≤1)
    (hSupports : MatrixConditionalMildSolution.Supports H Q G hH) :
    ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,∀ t : ℝ≥0,t≤H →
      MemLp (state H t) 2 (CanonicalInitialKernel.kernel H Q z) := by
  filter_upwards [hSupports,CanonicalInitialKernel.matching_initial H Q] with z hSolution hInitial
  obtain ⟨hBrown,hEq⟩ := hSolution
  have hi : state H 0 =ᵐ[CanonicalInitialKernel.kernel H Q z] fun _ => z := hInitial
  have hZ : MemLp (state H 0) 2 (CanonicalInitialKernel.kernel H Q z) :=
    (memLp_const z).ae_eq hi.symm
  intro t ht
  have hh := (VectorAnalyticHeat.heat (t : ℝ)).comp_memLp' hZ
  have hn := Lp.memLp (MatrixFourierMildRecognition.convolution (filtration H)
    (CanonicalInitialKernel.kernel H Q z) H G (fun p => state H p.1 p.2) (state_predictable H) hH
    (MatrixCanonicalFourierRecognition.family H (CanonicalInitialKernel.kernel H Q z) hBrown) t ht)
  exact (hh.add hn).ae_eq (hEq t ht).symm

/-- The conditional second moment grows at most by the uniform heat
noise cost. The bound is integrable against every L2 reached-state law. -/
theorem energy_bound (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×HaarNode) H))
    [IsProbabilityMeasure Q] (G : MatrixNonlinearCoefficient.Coefficient d) (hH : (H : ℝ)≤1)
    (hSupports : MatrixConditionalMildSolution.Supports H Q G hH) :
    ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,∀ t : ℝ≥0,t≤H →
      (∫ x,‖state H t x‖^2 ∂CanonicalInitialKernel.kernel H Q z)≤‖z‖^2+
        MatrixAnalyticKernel.constant d (NativeMatrixEquation.cap G)*(2*(t : ℝ)^(1/2 : ℝ)) := by
  filter_upwards [hSupports,CanonicalInitialKernel.matching_initial H Q] with z hSolution hInitial
  obtain ⟨hBrown,hEq⟩ := hSolution
  intro t ht
  exact MatrixWeakStateEnergy.bound G (fun p => state H p.1 p.2) (state_predictable H) hH
    (MatrixCanonicalFourierRecognition.family H (CanonicalInitialKernel.kernel H Q z) hBrown)
    (state H 0) z hInitial hEq t ht

/-- Reconstructing a conditional solution kernel under an L2 initial
law preserves the L2 moment needed at the next deterministic join. -/
theorem mixture_state_memLp (H : ℝ≥0)
    (Q : Measure (CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×HaarNode) H))
    [IsProbabilityMeasure Q] (G : MatrixNonlinearCoefficient.Coefficient d) (hH : (H : ℝ)≤1)
    (hSupports : MatrixConditionalMildSolution.Supports H Q G hH)
    (hInitial : MemLp (id : Physical (d := d) → Physical (d := d)) 2 (CanonicalInitialKernel.initialLaw H Q))
    (t : ℝ≥0) (ht : t≤H) : MemLp (state H t) 2 Q := by
  have hm : Measurable (state (E := Physical (d := d)) (ι := d×HaarNode) H t) :=
    (state_adapted H t).mono ((filtration H).le t) le_rfl
  have hMix := ConditionalKernelL2.memLp (CanonicalInitialKernel.initialLaw H Q)
    (CanonicalInitialKernel.kernel H Q) (fun p => state H t p.2) (hm.comp measurable_snd) hInitial
    ((state_memLp H Q G hH hSupports).mono (fun _ hz => hz t ht)) 1
    (MatrixAnalyticKernel.constant d (NativeMatrixEquation.cap G)*(2*(t : ℝ)^(1/2 : ℝ)))
    ((energy_bound H Q G hH hSupports).mono (fun z hz => by simpa only [one_mul] using hz t ht))
  rw [←CanonicalInitialKernel.reconstruct H Q]
  exact (memLp_map_measure_iff hm.stronglyMeasurable.aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hMix

end SHEStochastic.MatrixConditionalMildMoments
