module
public import Mathlib.Data.Finset.Sort
public import Mathlib.Basic.NNReal.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SHE.OrderedGridCover
open Set
open scoped NNReal

/-- Every finite observation grid is contained in an ordered sequence
starting at the actual restart time and constant after its last point. -/
theorem exists_cover (v b:ℝ≥0)(hvb:v≤b)(s:Finset ℝ≥0)
    (hs:∀t∈s,v≤t∧t≤b):
    ∃T:ℕ→ℝ≥0,Monotone T ∧ T 0=v ∧ (∀k,T k≤b) ∧ ∀t∈s,∃k,T k=t:=by
  classical
  let q:=insert v s
  have hq:q.Nonempty:=⟨v,Finset.mem_insert_self _ _⟩
  have hqc:0<q.card:=Finset.card_pos.mpr hq
  let e:=q.orderEmbOfFin rfl
  let T:ℕ→ℝ≥0:=fun k=>if hk:k<q.card then e ⟨k,hk⟩ else q.max' hq
  have hqbound:∀t∈q,v≤t∧t≤b:=by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl|ht
    · exact ⟨le_rfl,hvb⟩
    · exact hs t ht
  refine ⟨T,?_,?_,?_,?_⟩
  · intro k l hkl
    by_cases hl:l<q.card
    · have hk:k<q.card:=hkl.trans_lt hl
      simp only [T,dite_eq_left hk,dite_eq_left hl]
      exact e.monotone (by exact_mod_cast hkl)
    · by_cases hk:k<q.card
      · simp only [T,dite_eq_left hk,dite_eq_right hl]
        exact Finset.le_max' q _ (Finset.orderEmbOfFin_mem q rfl ⟨k,hk⟩)
      · simp only [T,dite_eq_right hk,dite_eq_right hl,le_refl]
  · have hmin:q.min' hq=v:=le_antisymm
      (Finset.min'_le q v (Finset.mem_insert_self _ _))
      (Finset.le_min' q hq v (fun t ht=>(hqbound t ht).1))
    simpa only [T,dite_eq_left hqc,e,Finset.orderEmbOfFin_zero rfl hqc,hmin]
  · intro k
    by_cases hk:k<q.card
    · simpa only [T,dite_eq_left hk] using (hqbound _ (Finset.orderEmbOfFin_mem q rfl ⟨k,hk⟩)).2
    · simpa only [T,dite_eq_right hk] using (hqbound _ (Finset.max'_mem q hq)).2
  · intro t ht
    have htq:t∈q:=Finset.mem_insert_of_mem ht
    obtain ⟨i,hi⟩:∃i:Fin q.card,e i=t:=by
      have hr: t∈Set.range e:=by rw [Finset.range_orderEmbOfFin];exact htq
      exact hr
    exact ⟨i.val,by simpa only [T,dite_eq_left i.isLt] using hi⟩
end SHE.OrderedGridCover
