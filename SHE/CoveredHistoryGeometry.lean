module

public import SHE.CoveredControlledCovariance
public import SHE.PhysicalParentGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.CoveredHistoryGeometry
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain PhysicalChainArrays PhysicalParentGeometry
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

theorem terminal_le_lower (k : ℕ) (p : History X k) (j : Fin k) :
    (carrier L k).terminal p≤lower L k p j := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases le_rfl (fun j => ?_) j
    exact ((carrier L k).nodeTime_mem p).2.trans (ih p.1 j)

theorem upper_le_initial (k : ℕ) (p : History X k) (j : Fin k) :
    upper L k p j ≤ initialTerminal L k p := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih => exact Fin.cases (terminal_le_initial L k p.1) (fun j => ih p.1 j) j

theorem lower_lt_upper (k : ℕ) (p : History X k) (hp : StrictHistory L k p) (j : Fin k) :
    lower L k p j<upper L k p j := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ih p.1 hp.1 j) j
    change (carrier L k).nodeTime p<(carrier L k).terminal p.1
    rw [show (carrier L k).nodeTime p=p.2.1 from ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩]
    exact hp.2.2

theorem disjoint (k : ℕ) (p : History X k) :
    ∀ j l : Fin k,j≠l → upper L k p j≤lower L k p l ∨ upper L k p l≤lower L k p j := by
  induction k with
  | zero => exact fun j => Fin.elim0 j
  | succ k ih =>
    intro j l
    refine Fin.cases ?_ (fun j => ?_) j
    · refine Fin.cases ?_ (fun l => ?_) l
      · exact fun hne => False.elim (hne rfl)
      · exact fun _ => Or.inl (terminal_le_lower L k p.1 l)
    · refine Fin.cases ?_ (fun l => ?_) l
      · exact fun _ => Or.inr (terminal_le_lower L k p.1 j)
      · exact fun hne => ih p.1 j l (fun h => hne (congrArg Fin.succ h))

theorem stop_dichotomy (k : ℕ) (p : History X k) (j : Fin k) (i : Fin (n+k)) :
    ((carrier L k).observations.observations p i).stop≤lower L k p j ∨
      upper L k p j≤((carrier L k).observations.observations p i).stop := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · refine Fin.cases (Or.inl le_rfl) (fun i => ?_) i
      exact Or.inr ((carrier L k).stops_after p.1 i)
    · refine Fin.cases ?_ (fun i => ih p.1 j i) i
      exact Or.inl (((carrier L k).nodeTime_mem p).2.trans (terminal_le_lower L k p.1 j))

theorem leafIndex_comp {N M : ℕ} (k : ℕ) (g : Fin (n+k)→Fin N) (f : Fin N→Fin M) (j : Fin k) :
    leafIndex k (fun i => f (g i)) j=f (leafIndex k g j) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih => exact Fin.cases rfl (fun j => ih (fun i => g i.succ) j) j

theorem leaf_observation (k : ℕ) (p : History X k) (j : Fin k) :
    (carrier L k).observations.observations p (leafIndex k (fun i => i) j)=
      ⟨lower L k p j,lower L k p j,space k p j⟩ := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · change Observation.mk ((carrier L k).nodeTime p) ((carrier L k).nodeTime p+0) p.2.2=_
      rw [add_zero]
      rfl
    · change (carrier L (k+1)).observations.observations p (leafIndex k (fun i => i.succ) j)=_
      rw [leafIndex_comp k (fun i => i) Fin.succ j]
      exact ih p.1 j

def lowerWith (k : ℕ) (p : History X k) (q : ℝ) : Fin (k+1)→ℝ :=
  Fin.cons q (lower L k p)

def upperWith (k : ℕ) (p : History X k) : Fin (k+1)→ℝ :=
  Fin.cons ((carrier L k).terminal p) (upper L k p)

theorem upperWith_le_initial (k : ℕ) (p : History X k) (j : Fin (k+1)) :
    upperWith L k p j ≤ initialTerminal L k p :=
  Fin.cases (terminal_le_initial L k p) (fun j => upper_le_initial L k p j) j

theorem lowerWith_bound (k : ℕ) (p : History X k) {q : ℝ} (hq : q≤(carrier L k).terminal p)
    (j : Fin (k+1)) : q≤lowerWith L k p q j :=
  Fin.cases le_rfl (fun j => hq.trans (terminal_le_lower L k p j)) j

theorem gapWith (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q : ℝ} (hq : q<(carrier L k).terminal p) (j : Fin (k+1)) :
    lowerWith L k p q j<upperWith L k p j :=
  Fin.cases hq (fun j => lower_lt_upper L k p hp j) j

theorem disjointWith (k : ℕ) (p : History X k) (q : ℝ) :
    ∀ j l : Fin (k+1),j≠l → upperWith L k p j≤lowerWith L k p q l ∨
      upperWith L k p l≤lowerWith L k p q j := by
  intro j l
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact fun hne => False.elim (hne rfl)
    · exact fun _ => Or.inl (terminal_le_lower L k p l)
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact fun _ => Or.inr (terminal_le_lower L k p j)
    · exact fun hne => disjoint L k p j l (fun h => hne (congrArg Fin.succ h))

theorem stopWith (k : ℕ) (p : History X k) (q : ℝ) (j : Fin (k+1)) (i : Fin (n+k)) :
    min ((carrier L k).observations.observations p i).stop (initialTerminal L k p)≤lowerWith L k p q j ∨
      upperWith L k p j≤min ((carrier L k).observations.observations p i).stop (initialTerminal L k p) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact Or.inr (le_min ((carrier L k).stops_after p i) (terminal_le_initial L k p))
  · rcases stop_dichotomy L k p j i with h|h
    · exact Or.inl ((min_le_left _ _).trans h)
    · exact Or.inr (le_min h (upper_le_initial L k p j))

end SHE.CoveredHistoryGeometry
