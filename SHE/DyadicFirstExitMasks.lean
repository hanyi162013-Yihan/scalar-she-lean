module
public import SHE.ApproximationCells
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.DyadicFirstExitMasks
open MeasureTheory Set Filter ApproximationCells ApproximationClock
open scoped NNReal Topology
variable {Ω:Type*}

def event(A:ℝ≥0→Ω→ℝ)(r:ℝ)(n i:ℕ):Set Ω:=
  {ω|r < A (point n i) ω ∧ ∀j,j < i →A (point n j) ω ≤ r}

theorem point_mono(n:ℕ):Monotone (point n):=by
  intro i j hij
  change delta n*(i:ℝ) ≤ delta n*(j:ℝ)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (delta_pos n).le

theorem point_lt(n:ℕ){s:ℝ≥0}(hs:0 < s){i:ℕ}(hi:i < index n s):point n i < s:=by
  have ht:(point n (index n s-1):ℝ) < (s:ℝ):=by
    rw [←left_eq_point n hs]
    exact (left_bounds n (by exact_mod_cast hs)).2.1
  have hp:=point_mono n (show i ≤ index n s-1 by omega)
  exact lt_of_le_of_lt hp (by exact_mod_cast ht)

section Measurable
variable [MeasurableSpace Ω](𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)

/-- Each first grid-exit event is known at that same grid time. -/
theorem measurable_event(A:ℝ≥0→Ω→ℝ)(ha:StronglyAdapted 𝓕 A)(r:ℝ)(n i:ℕ):
    MeasurableSet[𝓕 (point n i)] (event A r n i):=by
  have hb(j:ℕ):MeasurableSet[𝓕 (point n i)] {ω|j < i →A (point n j) ω ≤ r}:=by
    by_cases hji:j < i
    · simpa only [hji,forall_const] using measurableSet_le
        (((ha (point n j)).mono (𝓕.mono (point_mono n hji.le))).measurable) measurable_const
    · simp only [hji,IsEmpty.forall_iff,setOf_true]
      exact MeasurableSet.univ
  exact (measurableSet_lt measurable_const (ha (point n i)).measurable).inter
    (by convert (MeasurableSet.iInter hb) using 1; ext ω; simp only [Set.mem_iInter,Set.mem_setOf_eq]; rfl)
end Measurable

theorem disjoint(A:ℝ≥0→Ω→ℝ)(r:ℝ)(n:ℕ){i j:ℕ}(hij:i≠j):
    Disjoint (event A r n i) (event A r n j):=by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  rcases lt_or_gt_of_ne hij with hlt|hgt
  · exact (not_lt_of_ge (hj.2 i hlt)) hi.1
  · exact (not_lt_of_ge (hi.2 j hgt)) hj.1

theorem exists_event_le(A:ℝ≥0→Ω→ℝ)(r:ℝ)(n:ℕ)(ω:Ω){k:ℕ}
    (hk:r < A (point n k) ω):∃i:ℕ,i ≤ k ∧ ω∈event A r n i:=by
  have hex:∃i:ℕ,r < A (point n i) ω:=⟨k,hk⟩
  refine ⟨Nat.find hex,Nat.find_min' hex hk,Nat.find_spec hex,?_⟩
  intro j hj
  exact le_of_not_gt (Nat.find_min hex hj)

def mask(A:ℝ≥0→Ω→ℝ)(r:ℝ)(n:ℕ)(H s:ℝ≥0)(ω:Ω):ℝ:=by
  classical
  exact ∑i∈Finset.range (index n H),if ω∈event A r n i ∧ point n i < s then 1 else 0

theorem mask_eq_one(A:ℝ≥0→Ω→ℝ)(r:ℝ)(n:ℕ)(H s:ℝ≥0)(ω:Ω){i:ℕ}
    (hi:i < index n H)(he:ω∈event A r n i)(hs:point n i < s):mask A r n H s ω=1:=by
  classical
  unfold mask
  rw [Finset.sum_eq_single i]
  · simp only [he,hs,and_self,ite_true]
  · intro j _ hji
    apply if_neg
    rintro ⟨hj,_⟩
    exact Set.disjoint_left.mp (disjoint A r n hji) hj he
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hi))

/-- The finite sum never counts an exit twice. -/
theorem mask_zero_or_one(A:ℝ≥0→Ω→ℝ)(r:ℝ)(n:ℕ)(H s:ℝ≥0)(ω:Ω):
    mask A r n H s ω=0 ∨ mask A r n H s ω=1:=by
  classical
  by_cases he:∃i:ℕ,i < index n H ∧ ω∈event A r n i ∧ point n i < s
  · obtain ⟨i,hi,hE,hp⟩:=he
    exact Or.inr (mask_eq_one A r n H s ω hi hE hp)
  · left
    unfold mask
    apply Finset.sum_eq_zero
    intro i hi
    exact if_neg (fun h=>he ⟨i,Finset.mem_range.mp hi,h⟩)

theorem mask_bounds(A:ℝ≥0→Ω→ℝ)(r:ℝ)(n:ℕ)(H s:ℝ≥0)(ω:Ω):
    0 ≤ mask A r n H s ω ∧ mask A r n H s ω ≤ 1:=by
  rcases mask_zero_or_one A r n H s ω with he|he <;> rw [he] <;> norm_num

/-- Continuity and a strict threshold give a preceding grid exit at
every positive source time with cost above the threshold. -/
theorem mask_eventually_one(A:ℝ≥0→Ω→ℝ)(hc:∀ω,Continuous (fun t=>A t ω))
    (r:ℝ)(H s:ℝ≥0)(hs:0 < s)(hsH:s ≤ H)(ω:Ω)(hAr:r < A s ω):
    ∀ᶠn:ℕ in atTop,mask A r n H s ω=1:=by
  have hl:Tendsto (fun n=>point n (index n s-1)) atTop (𝓝 s):=by
    apply NNReal.tendsto_coe.mp
    have he:(fun n=>(point n (index n s-1):ℝ))=(fun n=>left n (s:ℝ)):=
      funext (fun n=>(left_eq_point n hs).symm)
    rw [he]
    exact left_tendsto s.2
  have ha:=((hc ω).continuousAt.tendsto.comp hl).eventually (lt_mem_nhds hAr)
  filter_upwards [ha] with n hn
  obtain ⟨i,hi,hE⟩:=exists_event_le A r n ω hn
  have hsidx:index n s ≤ index n H:=(Finset.mem_Icc.mp (index_mem n hs hsH)).2
  have hidx:0 < index n s:=(Finset.mem_Icc.mp (index_mem n hs hsH)).1
  exact mask_eq_one A r n H s ω (by omega) hE (point_lt n hs (by omega))

/-- Every mask vanishes on the genuine no-exit event. -/
theorem mask_no_exit(A:ℝ≥0→Ω→ℝ)(hm:∀ω,Monotone (fun t=>A t ω))
    (r:ℝ)(n:ℕ)(H s:ℝ≥0)(hH:0 < H)(ω:Ω)(hAr:A H ω ≤ r):mask A r n H s ω=0:=by
  classical
  unfold mask
  apply Finset.sum_eq_zero
  intro i hi
  apply if_neg
  rintro ⟨hE,_⟩
  have hp:=hm ω (point_lt n hH (Finset.mem_range.mp hi)).le
  exact (not_lt_of_ge (hp.trans hAr)) hE.1

end SHE.DyadicFirstExitMasks
