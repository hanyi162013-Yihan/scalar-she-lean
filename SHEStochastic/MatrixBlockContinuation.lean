module

public import SHEStochastic.MatrixGlobalBlockPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixBlockContinuation
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {hH : (H : ℝ)≤1}
    (D : MatrixLocalBlockChain.Data H G hH) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

/-- At the actual reached endpoint, the next kernel retains its full
canonical-past Brownian law and the original vector mild equation. -/
theorem future_solution (j : ℕ) :
    ∀ᵐ x ∂(D.blockLaw ρ₀ j).toMeasure,
      ∃ hBrown : ∀ m (a : Fin m → Fin n×HaarNode),FiniteBrownianLawOn (filtration H)
        (D.kernel ρ₀ j x) H (fun l => coordinate H (a l))
          (fun l k => if a l=a k then 1 else 0),
      MatrixFourierMildRecognition.Equation (filtration H) (D.kernel ρ₀ j x) H G
        (fun p => state H p.1 p.2) (state_predictable H) hH
        (MatrixCanonicalFourierRecognition.family H (D.kernel ρ₀ j x) hBrown) (state H 0) := by
  have h := (D.select (D.initialLaws ρ₀ (j+1))).supports
  change MatrixConditionalMildSolution.Supports H (D.blockLaw ρ₀ (j+1)).toMeasure G hH at h
  unfold MatrixConditionalMildSolution.Supports at h
  rw [←D.endpoint ρ₀ j] at h
  exact ae_of_ae_map (μ := (D.blockLaw ρ₀ j).toMeasure)
    (MatrixLocalBlockChain.state_measurable H H).aemeasurable h

variable {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

/-- The reached endpoint retains the full-past conditional Brownian law,
independently of the nonlinear equation being pasted. -/
theorem future_brownian (j : ℕ) :
    ∀ᵐ x ∂(D.blockLaw ρ₀ j).toMeasure,
      ∃ hBrown : ∀ m (a : Fin m → Fin n×HaarNode),FiniteBrownianLawOn (filtration H)
        (D.kernel ρ₀ j x) H (fun l => coordinate H (a l))
        (fun l k => if a l=a k then 1 else 0),True := by
  have h := D.brownian (D.initialLaws ρ₀ (j+1))
  change MatrixCanonicalBlockChain.Brownian H (D.blockLaw ρ₀ (j+1)) at h
  unfold MatrixCanonicalBlockChain.Brownian at h
  rw [←D.endpoint ρ₀ j] at h
  exact ae_of_ae_map (μ := (D.blockLaw ρ₀ j).toMeasure)
    (MatrixLocalBlockChain.state_measurable H H).aemeasurable h

/-- Brownian local coordinates start at zero under every selected
block law. This is derived from the conditional Brownian laws. -/
theorem local_zero (j : ℕ) (i : Fin n×HaarNode) :
    coordinate H i 0 =ᵐ[(D.blockLaw ρ₀ j).toMeasure] fun _ => (0 : ℝ) := by
  let Q := (D.blockLaw ρ₀ j).toMeasure
  have hs := D.brownian (D.initialLaws ρ₀ j)
  have hz : ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q,
      coordinate H i 0 =ᵐ[CanonicalInitialKernel.kernel H Q z] fun _ => (0 : ℝ) := by
    filter_upwards [hs] with z hSolution
    exact CanonicalInitialBrownianKernel.zero H (CanonicalInitialKernel.kernel H Q z) hSolution.1 i
  have hm : Measurable (coordinate (E := Physical (d := Fin n)) H i 0) :=
    (coordinate_adapted H i 0).mono ((filtration H).le 0) le_rfl
  have hJoint := Measure.ae_compProd_of_ae_ae
    ((measurableSet_eq_fun hm measurable_const).preimage measurable_snd) hz
  change coordinate H i 0 =ᵐ[Q] fun _ => (0 : ℝ)
  rw [←CanonicalInitialKernel.reconstruct H Q]
  exact (ae_map_iff measurable_snd.aemeasurable (measurableSet_eq_fun hm measurable_const)).mpr hJoint

/-- A single null set suffices for every local driver and every block. -/
theorem all_zero :
    ∀ᵐ p ∂D.law ρ₀,∀ (j : ℕ) (i : Fin n×HaarNode),coordinate H i 0 (p j)=0 := by
  apply ae_all_iff.mpr
  intro j
  have hz := ae_all_iff.mpr (local_zero D ρ₀ j)
  rw [←D.marginals ρ₀ j] at hz
  exact ae_of_ae_map (μ := D.law ρ₀) (measurable_pi_apply j).aemeasurable hz

/-- The literal pasted driver increment is exactly the new local
Brownian coordinate, simultaneously on all local windows. -/
theorem driver_increment (hH0 : 0<H) :
    ∀ᵐ p ∂D.law ρ₀,∀ (j : ℕ) (i : Fin n×HaarNode) (s : ℝ≥0),s≤H →
      MatrixGlobalBlockPath.driver H i ((j : ℝ≥0)*H+s) p-
        MatrixGlobalBlockPath.driver H i ((j : ℝ≥0)*H) p=coordinate H i s (p j) := by
  filter_upwards [all_zero D ρ₀] with p hp j i s hs
  rw [MatrixGlobalBlockPath.driver_increment H hH0 i p j s hs,hp j i,sub_zero]

end SHEStochastic.MatrixBlockContinuation
