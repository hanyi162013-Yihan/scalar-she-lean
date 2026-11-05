module

public import SHEStochastic.MatrixUnboundedBlockChain
public import SHEStochastic.MatrixUnboundedFourierPullback
public import SHEStochastic.MatrixGlobalBlockFourier

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalBlocks
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1} {H : ℝ≥0}
    (D : MatrixUnboundedBlockChain.Data G hG hβ hβ1 H)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (hH0 : 0<H)

def dynamics (k : ℕ) : MatrixUnboundedBlockChain.Dynamics G hG hβ hβ1 H (D.blockLaw ρ₀ k) :=
  Classical.choice (D.select (D.initialLaws ρ₀ k)).supports

def sourceEnergy (k : ℕ) : Integrable
    (fun p => ‖CanonicalStateDriverFiltration.state H p.1 p.2‖^2)
      (energyMeasure (D.blockLaw ρ₀ k).toMeasure H) :=
  MatrixUnboundedCanonicalInput.state_energy H (D.blockLaw ρ₀ k).toMeasure (dynamics D ρ₀ k).energy

/-- The selected full-path square energy remains finite after the
block law is placed in the countable global continuation space. -/
theorem pathEnergy (k : ℕ) :
    Integrable (fun p : MatrixGlobalBlockPath.Space (n := n) H => ‖(p k).1‖^2)
      (D.law ρ₀) := by
  let π : MatrixGlobalBlockPath.Space (n := n) H → MatrixLocalBlockChain.Space (n := n) H :=
    fun p => p k
  have hπ : MeasurePreserving π (D.law ρ₀) (D.blockLaw ρ₀ k).toMeasure :=
    ⟨measurable_pi_apply k, D.marginals ρ₀ k⟩
  exact hπ.integrable_comp_of_integrable (dynamics D ρ₀ k).energy

/-- The selected law solves the original unbounded equation before pullback. -/
theorem source_equation (k : ℕ) : MatrixUnboundedFourierPullback.Equation G hG hβ hβ1.le
    (fun p => CanonicalStateDriverFiltration.state H p.1 p.2)
    (CanonicalStateDriverFiltration.state_predictable H) (sourceEnergy D ρ₀ k)
    (MatrixCanonicalFourierRecognition.family H (D.blockLaw ρ₀ k).toMeasure (dynamics D ρ₀ k).brownian)
    (CanonicalStateDriverFiltration.state H 0) := by
  intro i a freq t ht
  filter_upwards [(dynamics D ρ₀ k).equation i a freq t ht] with x hx
  have h0 : x.1 (StoppedPathPasting.origin H)=CanonicalStateDriverFiltration.state H 0 x := by
    simp [CanonicalStateDriverFiltration.state,CanonicalStateDriverFiltration.clock,StoppedPathPasting.origin]
  dsimp only [CanonicalLinearFluctuation.value] at hx
  rw [min_eq_left ht,h0] at hx
  exact sub_eq_iff_eq_add'.mp hx

/-- The actual global block state retains finite predictable energy. -/
def blockEnergy (k : ℕ) : Integrable
    (fun p => ‖MatrixGlobalBlockFourier.state hH0 k p‖^2) (energyMeasure (D.law ρ₀) H) :=
  MatrixUnboundedFourierPullback.energy (MatrixGlobalBlockBundle.bundle H hH0 k)
    (MatrixGlobalBlockBundle.preserving D ρ₀ (hH0 := hH0) k)
    (fun p => CanonicalStateDriverFiltration.state H p.1 p.2) (sourceEnergy D ρ₀ k)

/-- Every unbounded block equation holds on the SINGLE global
probability space, in the shifted full state-and-driver filtration. -/
theorem equation (k : ℕ) : MatrixUnboundedFourierPullback.Equation G hG hβ hβ1.le
    (MatrixGlobalBlockFourier.state hH0 k) (MatrixGlobalBlockFourier.predictable hH0 k)
    (blockEnergy D ρ₀ hH0 k) (MatrixGlobalBlockFamily.family D ρ₀ hH0 k)
    (CanonicalStateDriverFiltration.state H 0 ∘ MatrixGlobalBlockBundle.bundle H hH0 k) := by
  exact MatrixUnboundedFourierPullback.equation
    (D := DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H))
    (MatrixGlobalBlockBundle.bundle H hH0 k)
    (MatrixGlobalBlockBundle.preserving D ρ₀ (hH0 := hH0) k)
    (MatrixGlobalBlockBundle.filtered H hH0 k) G hG hβ hβ1.le
    (fun p => CanonicalStateDriverFiltration.state H p.1 p.2)
    (CanonicalStateDriverFiltration.state_predictable H) (sourceEnergy D ρ₀ k)
    (MatrixCanonicalFourierRecognition.family H (D.blockLaw ρ₀ k).toMeasure (dynamics D ρ₀ k).brownian)
    (MatrixGlobalBlockFamily.family D ρ₀ hH0 k) (fun _ _ _ => rfl)
    (CanonicalStateDriverFiltration.state H 0) (source_equation D ρ₀ k)

end SHEStochastic.MatrixUnboundedGlobalBlocks
