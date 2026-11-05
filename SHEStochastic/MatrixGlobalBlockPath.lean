module

public import SHEStochastic.MatrixLocalBlockChain
public import SHEStochastic.CountablePathConcatenation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixGlobalBlockPath
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

abbrev Space (H : ℝ≥0) := ℕ → MatrixLocalBlockChain.Space (n := n) H

def state (H : ℝ≥0) (t : ℝ≥0) (p : Space (n := n) H) : Physical (d := Fin n) :=
  CountablePathConcatenation.value H (fun j s => MatrixLocalBlockChain.state H s (p j)) t

theorem continuous (H : ℝ≥0) (hH : 0<H) (p : Space (n := n) H) :
    Continuous (fun t => state H t p) :=
  CountablePathConcatenation.continuous H hH _
    (fun j => CanonicalStateDriverFiltration.state_continuous H (p j))

theorem measurable (H : ℝ≥0) :
    Measurable (fun q : ℝ≥0×Space (n := n) H => state H q.1 q.2) := by
  exact CountablePathConcatenation.measurable H
    (fun j (q : ℝ≥0×Space (n := n) H) => MatrixLocalBlockChain.state H q.1 (q.2 j))
    (fun j => (CanonicalStateDriverFiltration.state_joint_measurable H).comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))

/-- One continuous global state contains every genuine local solution
path, including both sides of each joining time. -/
theorem block {H : ℝ≥0} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))
    (hH0 : 0<H) :
    ∀ᵐ p ∂D.law ρ₀,∀ (j : ℕ) (s : ℝ≥0),s≤H →
      state H ((j : ℝ≥0)*H+s) p=MatrixLocalBlockChain.state H s (p j) := by
  filter_upwards [D.matching ρ₀] with p hp j s hs
  exact CountablePathConcatenation.block H hH0 _ hp j s hs

/-- Local L2 moments survive on the single global probability space. -/
theorem block_memLp {H : ℝ≥0} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))
    (hH0 : 0<H) (j : ℕ) (s : ℝ≥0) (hs : s≤H) :
    MemLp (state H ((j : ℝ≥0)*H+s)) 2 (D.law ρ₀) := by
  have hm := (D.select (D.initialLaws ρ₀ j)).moments s hs
  change MemLp (MatrixLocalBlockChain.state H s) 2 (D.blockLaw ρ₀ j).toMeasure at hm
  rw [←D.marginals ρ₀ j] at hm
  have hp : MemLp (fun p : Space (n := n) H => MatrixLocalBlockChain.state H s (p j)) 2 (D.law ρ₀) :=
    (memLp_map_measure_iff
      (MatrixLocalBlockChain.state_measurable H s).stronglyMeasurable.aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).mp hm
  exact MemLp.ae_eq ((block D ρ₀ hH0).mono fun p h => (h j s hs).symm) hp

theorem memLp {H : ℝ≥0} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))
    (hH0 : 0<H) (t : ℝ≥0) : MemLp (state H t) 2 (D.law ρ₀) := by
  obtain ⟨j,s,hs,he⟩ := CountablePathConcatenation.exists_block H hH0 t
  rw [←he]
  exact block_memLp D ρ₀ hH0 j s hs

/-- Local Brownian paths are pasted by increments, rather than by
identifying their absolute coordinate values at successive endpoints. -/
def driver (H : ℝ≥0) (i : Fin n×HaarNode) (t : ℝ≥0) (p : Space (n := n) H) : ℝ :=
  CountablePathConcatenation.value H
    (fun j s => CanonicalStateDriverFiltration.coordinate H i s (p j)) t

theorem driver_continuous (H : ℝ≥0) (hH : 0<H) (i : Fin n×HaarNode) (p : Space (n := n) H) :
    Continuous (fun t => driver H i t p) :=
  CountablePathConcatenation.continuous H hH _
    (fun j => CanonicalStateDriverFiltration.coordinate_continuous H i (p j))

theorem driver_measurable (H : ℝ≥0) (i : Fin n×HaarNode) :
    Measurable (fun q : ℝ≥0×Space (n := n) H => driver H i q.1 q.2) :=
  CountablePathConcatenation.measurable H
    (fun j (q : ℝ≥0×Space (n := n) H) => CanonicalStateDriverFiltration.coordinate H i q.1 (q.2 j))
    (fun j => (CanonicalStateDriverFiltration.coordinate_joint_measurable H i).comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))

theorem driver_increment (H : ℝ≥0) (hH : 0<H) (i : Fin n×HaarNode)
    (p : Space (n := n) H) (j : ℕ) (s : ℝ≥0) (hs : s≤H) :
    driver H i ((j : ℝ≥0)*H+s) p-driver H i ((j : ℝ≥0)*H) p=
      CanonicalStateDriverFiltration.coordinate H i s (p j)-
        CanonicalStateDriverFiltration.coordinate H i 0 (p j) :=
  CountablePathConcatenation.increment H hH _ j s hs

end SHEStochastic.MatrixGlobalBlockPath
