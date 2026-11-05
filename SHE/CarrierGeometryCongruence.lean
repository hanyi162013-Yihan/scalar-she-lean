module

public import SHE.CutoffCarriers
public import SHE.UncutSmoothWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.CarrierGeometryCongruence
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
variable {X : Type} [MeasurableSpace X] {n : ℕ} {R Q : ReferenceData}
variable (L : Level R X n) (K : Level Q X n) (hb : R.base=Q.base)
  (hT : ∀ x,L.terminal x=K.terminal x)
  (hZ : ∀ x,L.observations.observations x=K.observations.observations x)

include hb hT

/-- Carrier geometry depends only on the base, original terminal times
and original observations. The reference covariance and test are absent. -/
theorem terminal (k : ℕ) (p : History X k) :
    (carrier L k).terminal p=(carrier K k).terminal p := by
  induction k with
  | zero => exact hT p
  | succ k ih =>
    change ClippedCovariance.clip R.base ((carrier L k).terminal p.1) p.2.1=
      ClippedCovariance.clip Q.base ((carrier K k).terminal p.1) p.2.1
    rw [hb,ih p.1]

theorem nodeTime (k : ℕ) (p : History X (k+1)) :
    (carrier L k).nodeTime p=(carrier K k).nodeTime p := by
  change ClippedCovariance.clip R.base ((carrier L k).terminal p.1) p.2.1=
    ClippedCovariance.clip Q.base ((carrier K k).terminal p.1) p.2.1
  rw [hb,terminal L K hb hT k p.1]

include hZ in
theorem observations (k : ℕ) (p : History X k) :
    (carrier L k).observations.observations p=(carrier K k).observations.observations p := by
  induction k with
  | zero => exact hZ p
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j=>congrFun (ih p.1) j) i
    change Observation.mk ((carrier L k).nodeTime p) ((carrier L k).nodeTime p+0) p.2.2=
      Observation.mk ((carrier K k).nodeTime p) ((carrier K k).nodeTime p+0) p.2.2
    rw [nodeTime L K hb hT k p]

theorem interior_iff (k : ℕ) (p : History X (k+1)) : Interior L k p↔Interior K k p := by
  change (R.base<p.2.1 ∧ p.2.1<(carrier L k).terminal p.1)↔
    (Q.base<p.2.1 ∧ p.2.1<(carrier K k).terminal p.1)
  rw [hb,terminal L K hb hT k p.1]

include hZ in
theorem row (k : ℕ) (p : History X (k+1)) : CutoffCarriers.row L k p=CutoffCarriers.row K k p := by
  classical
  have he:=interior_iff L K hb hT k p
  by_cases h : Interior L k p
  · have h':=he.mp h
    simp only [CutoffCarriers.row,h,h',ite_true]
    rw [observations L K hb hT hZ k p.1,nodeTime L K hb hT k p]
  · have h':=mt he.mpr h
    simp only [CutoffCarriers.row,h,h',ite_false]

include hZ in
theorem weight (k : ℕ) (p : History X k) :
    UncutSmoothWords.weight L k p=UncutSmoothWords.weight K k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change UncutSmoothWords.weight L k p.1*‖CutoffCarriers.row L k p‖^2=
      UncutSmoothWords.weight K k p.1*‖CutoffCarriers.row K k p‖^2
    rw [ih p.1,row L K hb hT hZ k p]

end SHE.CarrierGeometryCongruence
