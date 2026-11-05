module

public import SHEStochastic.MatrixGlobalBlockPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.MatrixBlockNaturalFiltration
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0)

/-- The global past keeps completed blocks and the current local
state-and-driver past. Later blocks are set to the fixed zero path;
their future initial states are not revealed in advance. -/
def history (t : ℝ≥0) (p : MatrixGlobalBlockPath.Space (n := n) H) :
    MatrixGlobalBlockPath.Space (n := n) H := fun j =>
  if (j : ℝ≥0)*H<t ∨ j=0 then
    CanonicalStateDriverFiltration.history H (t-(j : ℝ≥0)*H) (p j)
  else 0

theorem history_measurable (t : ℝ≥0) : Measurable (history (n := n) H t) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : (j : ℝ≥0)*H<t ∨ j=0
  · simpa only [history,if_pos hj,Function.comp_def] using
      (CanonicalStateDriverFiltration.history_measurable (E := Physical (d := Fin n))
        (ι := Fin n×HaarNode) H (t-(j : ℝ≥0)*H)).comp (measurable_pi_apply j)
  · simpa only [history,if_neg hj] using
      (measurable_const (a := (0 : MatrixLocalBlockChain.Space (n := n) H)))

theorem history_comp (s t : ℝ≥0) (hst : s≤t) :
    history (n := n) H s ∘ history H t=history H s := by
  funext p j
  by_cases hs : (j : ℝ≥0)*H<s ∨ j=0
  · have ht : (j : ℝ≥0)*H<t ∨ j=0 :=
      hs.elim (fun h => Or.inl (h.trans_le hst)) Or.inr
    simp only [Function.comp_apply,history,if_pos hs,if_pos ht]
    exact congrFun (CanonicalStateDriverFiltration.history_comp
      (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H
      (s-(j : ℝ≥0)*H) (t-(j : ℝ≥0)*H) (tsub_le_tsub_right hst _)) (p j)
  · simp only [Function.comp_apply,history,if_neg hs]

/-- One filtration on the actual infinite continuation space, retaining
both states and drivers through the current physical time. -/
def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (MatrixGlobalBlockPath.Space (n := n) H)) where
  seq t := MeasurableSpace.comap (history H t) inferInstance
  mono' s t hst := by
    have hc := history_comp (n := n) H s t hst
    calc
      _ = MeasurableSpace.comap (history H t) (MeasurableSpace.comap (history H s) inferInstance) := by
        rw [MeasurableSpace.comap_comp,hc]
      _ ≤ _ := MeasurableSpace.comap_mono (history_measurable H s).comap_le
  le' t := (history_measurable H t).comap_le

end SHEStochastic.MatrixBlockNaturalFiltration
