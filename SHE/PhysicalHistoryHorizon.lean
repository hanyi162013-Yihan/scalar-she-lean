module

public import SHE.ScoreSpatialSections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PhysicalParentGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- Every appended heat target stays below the same original target
horizon, including inactive clipped histories. -/
theorem carrier_targets_le (T : ℝ) (hterm : ∀ p,L.terminal p ≤ T)
    (hroot : ∀ p i,(L.observations.observations p i).target ≤ T) (k : ℕ) :
    ∀ p i,((carrier L k).observations.observations p i).target ≤ T := by
  induction k with
  | zero => exact hroot
  | succ k ih =>
    intro p i
    refine Fin.cases ?_ (fun j => ih p.1 j) i
    change (carrier L k).nodeTime p+0 ≤ T
    rw [add_zero]
    exact ((carrier L k).nodeTime_mem p).2.trans
      ((terminal_le_initial L k p.1).trans (hterm _))

/-- A small common original horizon discharges all earlier-frame age
conditions in a fixed finite-order score estimate. -/
theorem smallHistory_of_horizon (T : ℝ) (hterm : ∀ p,L.terminal p ≤ T)
    (hroot : ∀ p i,(L.observations.observations p i).target ≤ T)
    (H : ℕ → ℝ) (k : ℕ) (hH : ∀ j,j<k → T ≤ H j) (p : History P k) :
    SmallHistory L H k p := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨ih (fun j hj => hH j (Nat.lt_trans hj (Nat.lt_succ_self k))) p.1,?_⟩
    intro i
    have ht := carrier_targets_le L T hterm hroot k p.1 i
    have hn : 0 ≤ (carrier L k).nodeTime p :=
      R.base_nonneg.trans ((carrier L k).nodeTime_mem p).1
    exact (sub_le_self _ hn).trans (ht.trans (hH k (Nat.lt_succ_self k)))

/-- The fresh terminal heat-span horizon is likewise automatic from the
original target bound at every nonnegative current time. -/
theorem carrier_age_le (T : ℝ) (hterm : ∀ p,L.terminal p ≤ T)
    (hroot : ∀ p i,(L.observations.observations p i).target ≤ T)
    (k : ℕ) (p : History P k) {q : ℝ} (hq : 0 ≤ q) (i : Fin (n+k)) :
    ((carrier L k).observations.observations p i).target-q ≤ T :=
  (sub_le_self _ hq).trans (carrier_targets_le L T hterm hroot k p i)

end SHE.PhysicalParentGeometry
