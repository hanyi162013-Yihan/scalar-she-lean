module

public import SHEStochastic.CanonicalBlockPastEval
public import SHEStochastic.MatrixBlockNaturalFiltration
public import SHEStochastic.CountablePathFiniteSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixBlockProcessAdapted
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixBlockNaturalFiltration
open CountablePathConcatenation CountablePathFiniteSum NNRealBlockClock
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0)

section Observable
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (f : ℝ≥0 → MatrixLocalBlockChain.Space (n := n) H → E)
    (hPast : ∀ s t x,f t (CanonicalStateDriverFiltration.history H s x)=f (min t s) x)

include hPast in
/-- The anchored global path depends only on the actual physical past.
The assertion is pointwise, even for nonmatching exceptional block paths. -/
theorem value_history (hH : 0<H) (t : ℝ≥0) (p : MatrixGlobalBlockPath.Space (n := n) H) :
    value H (fun j s => f s (history H t p j)) t=value H (fun j s => f s (p j)) t := by
  let M := ⌈t/H⌉₊
  have hc := covering H t hH
  rw [value_sum H hH _ M t hc,value_sum H hH _ M t hc]
  have h0 : f (clock H 0 t) (history H t p 0)=f (clock H 0 t) (p 0) := by
    simp only [history,Nat.cast_zero,zero_mul,tsub_zero,or_true,ite_true]
    rw [hPast,min_eq_left (show clock H 0 t≤t from by simp [clock])]
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ((j+1 : ℕ) : ℝ≥0)*H<t ∨ j+1=0
  · simp only [history,if_pos hj]
    rw [hPast,hPast,min_eq_left (show clock H (j+1) t≤t-((j+1 : ℕ) : ℝ≥0)*H from min_le_left _ _),
      min_eq_left (show (0 : ℝ≥0)≤t-((j+1 : ℕ) : ℝ≥0)*H from bot_le)]
  · have ht : t≤((j+1 : ℕ) : ℝ≥0)*H := le_of_not_gt (fun ht => hj (Or.inl ht))
    have hz : clock H (j+1) t=0 := by
      change min (t-((j+1 : ℕ) : ℝ≥0)*H) H=0
      rw [tsub_eq_zero_of_le ht,min_eq_left (show (0 : ℝ≥0)≤H from bot_le)]
    simp only [hz,sub_self]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

include hPast in
theorem measurable (hH : 0<H)
    (hf : Measurable (fun z : ℝ≥0×MatrixLocalBlockChain.Space (n := n) H => f z.1 z.2)) (t : ℝ≥0) :
    Measurable[filtration (n := n) H t] (fun p => value H (fun j s => f s (p j)) t) := by
  have hm : Measurable (fun p : MatrixGlobalBlockPath.Space (n := n) H => value H (fun j s => f s (p j)) t) :=
    (CountablePathConcatenation.measurable H (fun j (z : ℝ≥0×MatrixGlobalBlockPath.Space (n := n) H) => f z.1 (z.2 j))
      (fun j => hf.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))).comp
        (measurable_const.prodMk measurable_id)
  have he : (fun p : MatrixGlobalBlockPath.Space (n := n) H => value H (fun j s => f s (p j)) t) ∘ history H t=
      (fun p => value H (fun j s => f s (p j)) t) := funext (value_history H f hPast hH t)
  have hh : Measurable[filtration (n := n) H t]
      ((fun p : MatrixGlobalBlockPath.Space (n := n) H => value H (fun j s => f s (p j)) t) ∘ history H t) :=
    hm.comp (Measurable.of_comap_le le_rfl)
  rwa [he] at hh
end Observable

theorem state_adapted (hH : 0<H) :
    StronglyAdapted (filtration (n := n) H) (MatrixGlobalBlockPath.state H) := by
  intro t
  exact (measurable H (CanonicalStateDriverFiltration.state H)
    (CanonicalBlockPastEval.state H) hH (CanonicalStateDriverFiltration.state_joint_measurable H) t).stronglyMeasurable

theorem driver_adapted (hH : 0<H) (i : Fin n×HaarNode) :
    StronglyAdapted (filtration (n := n) H) (MatrixGlobalBlockPath.driver H i) := by
  intro t
  exact (measurable H (CanonicalStateDriverFiltration.coordinate H i)
    (fun s t x => CanonicalBlockPastEval.coordinate H s t i x) hH
    (CanonicalStateDriverFiltration.coordinate_joint_measurable H i) t).stronglyMeasurable

theorem state_predictable (hH : 0<H) :
    StronglyMeasurable[(filtration (n := n) H).predictable]
      (fun z : ℝ≥0×MatrixGlobalBlockPath.Space (n := n) H => MatrixGlobalBlockPath.state H z.1 z.2) :=
  ContinuousPredictable.stronglyMeasurable (filtration H) _ (state_adapted H hH)
    (MatrixGlobalBlockPath.continuous H hH)

end SHEStochastic.MatrixBlockProcessAdapted
