module

public import SHEStochastic.CanonicalInitialBrownianKernel
public import SHEStochastic.KernelMarkovTrajectory
public import SHEStochastic.MatrixInfiniteHaar

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixLocalBlockChain
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

def L2Law := {ρ : ProbabilityMeasure (Physical (d := Fin n)) //
  MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2 ρ.toMeasure}

abbrev Space (H : ℝ≥0) := CanonicalContinuousStateDriver.Space
  (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H

def state (H t : ℝ≥0) : Space (n := n) H → Physical (d := Fin n) :=
  CanonicalStateDriverFiltration.state H t

theorem state_measurable (H t : ℝ≥0) : Measurable (state (n := n) H t) :=
  (CanonicalStateDriverFiltration.state_adapted H t).mono
    ((CanonicalStateDriverFiltration.filtration H).le t) le_rfl

end SHEStochastic.MatrixLocalBlockChain

namespace SHEStochastic.MatrixCanonicalBlockChain
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixLocalBlockChain
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

/-- Conditional Brownian drivers, independently of the particular equation. -/
def Brownian (H : ℝ≥0) (Q : ProbabilityMeasure (Space (n := n) H)) : Prop :=
  ∀ᵐ z ∂CanonicalInitialKernel.initialLaw H Q.toMeasure,
    ∃ hBrown : ∀ m (j : Fin m → Fin n×HaarNode),FiniteBrownianLawOn
      (CanonicalStateDriverFiltration.filtration H) (CanonicalInitialKernel.kernel H Q.toMeasure z) H
      (fun i => CanonicalStateDriverFiltration.coordinate H (j i))
      (fun i k => if j i=j k then 1 else 0),True

structure Block (H : ℝ≥0) (Supports : ProbabilityMeasure (Space (n := n) H) → Prop)
    (ρ : L2Law (n := n)) where
  law : ProbabilityMeasure (Space (n := n) H)
  initial : CanonicalInitialKernel.initialLaw H law.toMeasure=ρ.val.toMeasure
  supports : Supports law
  moments : ∀ t : ℝ≥0,t≤H → MemLp (state H t) 2 law.toMeasure

/-- Dynamics are retained as a parameter; the same Markov trajectory,
matching, and Brownian pasting apply to bounded and unbounded equations. -/
structure Data (H : ℝ≥0) (Supports : ProbabilityMeasure (Space (n := n) H) → Prop) where
  select : ∀ ρ : L2Law (n := n),Block H Supports ρ
  brownian : ∀ ρ,Brownian H (select ρ).law

variable {H : ℝ≥0} {Supports : ProbabilityMeasure (Space (n := n) H) → Prop}

def Data.next (D : Data H Supports) (ρ : L2Law (n := n)) : L2Law (n := n) := by
  let Q := (D.select ρ).law
  let ν := Q.toMeasure.map (state H H)
  letI : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (state_measurable H H).aemeasurable).mpr inferInstance
  refine ⟨⟨ν,inferInstance⟩,?_⟩
  exact (memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
    (state_measurable H H).aemeasurable).mpr ((D.select ρ).moments H le_rfl)

def Data.initialLaws (D : Data H Supports) (ρ₀ : L2Law (n := n)) : ℕ → L2Law (n := n)
  | 0 => ρ₀
  | j+1 => D.next (D.initialLaws ρ₀ j)

def Data.blockLaw (D : Data H Supports) (ρ₀ : L2Law (n := n)) (j : ℕ) : ProbabilityMeasure (Space (n := n) H) :=
  (D.select (D.initialLaws ρ₀ j)).law

theorem Data.initial_law (D : Data H Supports) (ρ₀ : L2Law (n := n)) (j : ℕ) :
    CanonicalInitialKernel.initialLaw H (D.blockLaw ρ₀ j).toMeasure=(D.initialLaws ρ₀ j).val.toMeasure :=
  (D.select (D.initialLaws ρ₀ j)).initial

theorem Data.endpoint (D : Data H Supports) (ρ₀ : L2Law (n := n)) (j : ℕ) :
    (D.blockLaw ρ₀ j).toMeasure.map (state H H)=
      CanonicalInitialKernel.initialLaw H (D.blockLaw ρ₀ (j+1)).toMeasure := by
  rw [D.initial_law]
  rfl

def Data.kernel (D : Data H Supports) (ρ₀ : L2Law (n := n)) (j : ℕ) : Kernel (Space (n := n) H) (Space (n := n) H) :=
  (CanonicalInitialKernel.kernel H (D.blockLaw ρ₀ (j+1)).toMeasure).comap (state H H) (state_measurable H H)

instance (D : Data H Supports) (ρ₀ : L2Law (n := n)) (j : ℕ) : IsMarkovKernel (D.kernel ρ₀ j) := by
  unfold Data.kernel
  infer_instance

/-- The next Borel kernel reconstructs exactly the selected next
block law. Thus every block has the genuine weak solution law, rather
than only a selected endpoint distribution. -/
theorem Data.step_law (D : Data H Supports) (ρ₀ : L2Law (n := n)) (j : ℕ) :
    (D.kernel ρ₀ j) ∘ₘ (D.blockLaw ρ₀ j).toMeasure=(D.blockLaw ρ₀ (j+1)).toMeasure := by
  let κ := CanonicalInitialKernel.kernel H (D.blockLaw ρ₀ (j+1)).toMeasure
  change (D.blockLaw ρ₀ j).toMeasure.bind (fun x => κ (state H H x))=_
  rw [←Measure.bind_map (state_measurable H H).aemeasurable κ.aemeasurable,D.endpoint]
  have he := CanonicalInitialKernel.reconstruct H (D.blockLaw ρ₀ (j+1)).toMeasure
  change ((CanonicalInitialKernel.initialLaw H (D.blockLaw ρ₀ (j+1)).toMeasure) ⊗ₘ κ).snd=_ at he
  rw [Measure.snd_compProd] at he
  exact he

def Data.law (D : Data H Supports) (ρ₀ : L2Law (n := n)) : Measure (ℕ → Space (n := n) H) :=
  KernelMarkovTrajectory.law (D.blockLaw ρ₀ 0).toMeasure (D.kernel ρ₀)

instance (D : Data H Supports) (ρ₀ : L2Law (n := n)) : IsProbabilityMeasure (D.law ρ₀) :=
  inferInstanceAs (IsProbabilityMeasure (KernelMarkovTrajectory.law (D.blockLaw ρ₀ 0).toMeasure (D.kernel ρ₀)))

/-- An actual infinite probability space of successive local weak
solutions, with every prescribed block law and all its L2 moments. -/
theorem Data.marginals (D : Data H Supports) (ρ₀ : L2Law (n := n)) :
    ∀ j,(D.law ρ₀).map (fun p => p j)=(D.blockLaw ρ₀ j).toMeasure :=
  KernelMarkovTrajectory.marginals (D.blockLaw ρ₀ 0).toMeasure (D.kernel ρ₀)
    (fun j => (D.blockLaw ρ₀ j).toMeasure) rfl (D.step_law ρ₀)

/-- Every actual continuation starts at the preceding endpoint,
simultaneously for the countably many blocks. -/
theorem Data.matching (D : Data H Supports) (ρ₀ : L2Law (n := n)) :
    ∀ᵐ p ∂D.law ρ₀,∀ j,state H 0 (p (j+1))=state H H (p j) := by
  apply ae_all_iff.mpr
  intro j
  apply KernelMarkovTrajectory.ae_step (D.blockLaw ρ₀ 0).toMeasure (D.kernel ρ₀) j
    (fun x y => state H 0 y=state H H x)
    (measurableSet_eq_fun ((state_measurable H 0).comp measurable_snd)
      ((state_measurable H H).comp measurable_fst))
  change ∀ᵐ x ∂(D.law ρ₀).map (fun p => p j),∀ᵐ y ∂D.kernel ρ₀ j x,state H 0 y=state H H x
  rw [D.marginals ρ₀ j]
  have hm := CanonicalInitialKernel.matching_initial H (D.blockLaw ρ₀ (j+1)).toMeasure
  rw [←D.endpoint ρ₀ j] at hm
  exact ae_of_ae_map (μ := (D.blockLaw ρ₀ j).toMeasure)
    (p := fun z => ∀ᵐ y ∂CanonicalInitialKernel.kernel H (D.blockLaw ρ₀ (j+1)).toMeasure z,
      state H 0 y=z) (state_measurable H H).aemeasurable hm

end SHEStochastic.MatrixCanonicalBlockChain
