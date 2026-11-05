module

public import SHEStochastic.MatrixFourierBlockChain
public import SHEStochastic.MatrixGlobalBlockFamily
public import SHEStochastic.MatrixFourierPullback

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixGlobalBlockFourier
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {C β : ℝ≥0}
    {hG : HolderWith C β G.value} {hβ : 0<β} {hβ1 : β≤1} {hH : (H : ℝ)≤1}
    (D : MatrixFourierBlockChain.Data H G hG hβ hβ1 hH)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (hH0 : 0<H)

def state (k : ℕ) : ℝ≥0×MatrixGlobalBlockPath.Space (n := n) H → Physical (d := Fin n) :=
  MatrixFourierPullback.state (MatrixGlobalBlockBundle.bundle H hH0 k)
    (fun p => CanonicalStateDriverFiltration.state H p.1 p.2)

theorem predictable (k : ℕ) :
    StronglyMeasurable[(DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration (n := n) H) ((k : ℝ≥0)*H)).predictable]
      (state (n := n) hH0 k) :=
  MatrixFourierPullback.predictable
    (D := DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H))
    (MatrixGlobalBlockBundle.bundle H hH0 k)
    (MatrixGlobalBlockBundle.filtered H hH0 k)
    (fun p => CanonicalStateDriverFiltration.state H p.1 p.2)
    (CanonicalStateDriverFiltration.state_predictable H)

/-- Every local Fourier equation holds on the actual pasted probability
space, in the shifted full global state-and-driver filtration. The
initial state and all stochastic integrals use the same filtered bundle. -/
theorem equation (k : ℕ) :
    MatrixFourierMildRealization.RandomEquation
      (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H))
      (D.base.law ρ₀) H (MatrixSmoothCoefficient.coefficient G 0)
      (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
      (state hH0 k) (predictable (n := n) hH0 k)
      (MatrixGlobalBlockFamily.family D.base ρ₀ hH0 k)
      (CanonicalStateDriverFiltration.state H 0 ∘ MatrixGlobalBlockBundle.bundle H hH0 k) := by
  exact MatrixFourierPullback.equation
    (D := DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H))
    (MatrixGlobalBlockBundle.bundle H hH0 k)
    (MatrixGlobalBlockBundle.preserving D.base ρ₀ (hH0 := hH0) k)
    (MatrixGlobalBlockBundle.filtered H hH0 k)
    (MatrixSmoothCoefficient.coefficient G 0) (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
    (fun p => CanonicalStateDriverFiltration.state H p.1 p.2)
    (CanonicalStateDriverFiltration.state_predictable H)
    (MatrixCanonicalFourierRecognition.family H (D.base.blockLaw ρ₀ k).toMeasure (MatrixFourierBlockChain.block_brownian D ρ₀ k))
    (MatrixGlobalBlockFamily.family D.base ρ₀ hH0 k) (fun _ _ _ => rfl)
    (CanonicalStateDriverFiltration.state H 0) (MatrixFourierBlockChain.block_fourier D ρ₀ k)

theorem state_eq (k : ℕ) (t : ℝ≥0) (ht : t≤H) (p : MatrixGlobalBlockPath.Space (n := n) H) :
    state hH0 k (t,p)=MatrixGlobalBlockPath.state H ((k : ℝ≥0)*H+t) p := by
  change CanonicalStateDriverFiltration.state H t (MatrixGlobalBlockBundle.bundle H hH0 k p)=_
  exact CanonicalStateDriverFiltration.state_bundle H (MatrixGlobalBlockPath.state H)
    (MatrixGlobalBlockPath.continuous H hH0) (MatrixGlobalBlockPath.driver H)
    (MatrixGlobalBlockPath.driver_continuous H hH0) ((k : ℝ≥0)*H) t ht p

end SHEStochastic.MatrixGlobalBlockFourier
