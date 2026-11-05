module

public import SHE.PhysicalHistoryHorizon
public import SHE.CoveredControlledLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.RelativeHistoryGeometry
open Set MeasureTheory WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalScoreChain PhysicalChainArrays PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- Every physical old-frame heat age is bounded by the original LOCAL
span T-base, rather than by the absolute endpoint T. -/
theorem smallHistory_of_span (T : ℝ) (hterm : ∀ p,L.terminal p ≤ T)
    (hroot : ∀ p i,(L.observations.observations p i).target ≤ T)
    (H : ℕ→ℝ) (k : ℕ) (hH : ∀ j,j<k→T-R.base ≤ H j) (p : History X k) :
    SmallHistory L H k p := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨ih (fun j hj=>hH j (Nat.lt_trans hj (Nat.lt_succ_self k))) p.1,?_⟩
    intro i
    have ht:=carrier_targets_le L T hterm hroot k p.1 i
    have hn:=((carrier L k).nodeTime_mem p).1
    linarith [hH k (Nat.lt_succ_self k)]

theorem carrier_age_le_span (T : ℝ) (hterm : ∀ p,L.terminal p ≤ T)
    (hroot : ∀ p i,(L.observations.observations p i).target ≤ T)
    (k : ℕ) (p : History X k) {q : ℝ} (hq : R.base ≤ q) (i : Fin (n+k)) :
    ((carrier L k).observations.observations p i).target-q ≤ T-R.base := by
  have ht:=carrier_targets_le L T hterm hroot k p i
  linarith

theorem relative_stop_pos (k : ℕ) (p : History X k) {q : ℝ}
    (hb : R.base ≤ q) (hq : q<(carrier L k).terminal p) (i : Fin (n+k)) :
    0<stops L k p i-R.base := by
  have hs : (carrier L k).terminal p ≤ stops L k p i:=
    le_min ((carrier L k).stops_after p i) (terminal_le_initial L k p)
  linarith

theorem relative_stop_le_span (T : ℝ) (hterm : ∀ p,L.terminal p ≤ T)
    (k : ℕ) (p : History X k) (i : Fin (n+k)) :
    stops L k p i-R.base ≤ T-R.base := by
  have hs : stops L k p i ≤ T:=(min_le_right _ _).trans (hterm (rootParameter k p))
  linarith

theorem native_leaf (k : ℕ) (p : History X k) (hp : StrictHistory L k p) (j : Fin k) :
    stops L k p (leafIndex k (fun i=>i) j)=targets L k p (leafIndex k (fun i=>i) j) := by
  unfold stops targets
  rw [leaf_observation L k p j]
  exact min_eq_left ((lower_lt_upper L k p hp j).le.trans (upper_le_initial L k p j))

theorem native_leaf_relative_age (T ageBound : ℝ) (hterm : ∀ p,L.terminal p ≤ T)
    (hspan : T-R.base ≤ ageBound) (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q : ℝ} (hb : R.base ≤ q) (hq : q<(carrier L k).terminal p) (j : Fin k) :
    targets L k p (leafIndex k (fun i=>i) j)-R.base∈Ioc 0 ageBound := by
  rw [←native_leaf L k p hp j]
  exact ⟨relative_stop_pos L k p hb hq _,(relative_stop_le_span L T hterm k p _).trans hspan⟩

/-- Relative old intervals preserve every original stop dichotomy,
including inactive leaves; clipping at the original covered endpoint
remains literal. -/
theorem relative_stop_dichotomy (k : ℕ) (p : History X k) (j : Fin k) (i : Fin (n+k)) :
    stops L k p i-R.base ≤ lower L k p j-R.base ∨
      upper L k p j-R.base ≤ stops L k p i-R.base := by
  rcases stop_dichotomy L k p j i with h|h
  · exact Or.inl (sub_le_sub_right ((min_le_left _ _).trans h) _)
  · exact Or.inr (sub_le_sub_right (le_min h (upper_le_initial L k p j)) _)

theorem relative_disjoint (k : ℕ) (p : History X k) (j l : Fin k) (hne : j≠l) :
    upper L k p j-R.base ≤ lower L k p l-R.base ∨
      upper L k p l-R.base ≤ lower L k p j-R.base := by
  exact (disjoint L k p j l hne).imp (fun h=>sub_le_sub_right h _) (fun h=>sub_le_sub_right h _)

end SHE.RelativeHistoryGeometry
