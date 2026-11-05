module

public import SHE.CarrierGeometryCongruence
public import SHE.PhysicalScoreProduct

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.CarrierPhysicalCongruence
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry StoppedGaussianFeatures
variable {X : Type} [MeasurableSpace X] {n N : ℕ} {R Q : ReferenceData}
variable (L : Level R X n) (K : Level Q X n) (hb : R.base=Q.base)
  (hT : ∀ x,L.terminal x=K.terminal x)
  (hZ : ∀ x,L.observations.observations x=K.observations.observations x)
include hb hT

theorem lower (k : ℕ) (p : History X k) :
    PhysicalChainArrays.lower L k p=PhysicalChainArrays.lower K k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    exact Fin.cases (CarrierGeometryCongruence.nodeTime L K hb hT k p)
      (fun j=>congrFun (ih p.1) j) i

theorem upper (k : ℕ) (p : History X k) :
    PhysicalChainArrays.upper L k p=PhysicalChainArrays.upper K k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    exact Fin.cases (CarrierGeometryCongruence.terminal L K hb hT k p.1)
      (fun j=>congrFun (ih p.1) j) i

theorem direction (Z : Fin N→Observation) (k : ℕ) (p : History X (k+1)) :
    PhysicalScoreChain.direction L Z k p=PhysicalScoreChain.direction K Z k p := by
  classical
  have he:=CarrierGeometryCongruence.interior_iff L K hb hT k p
  by_cases h : Interior L k p
  · have h':=he.mp h
    simp only [PhysicalScoreChain.direction,h,h',ite_true]
    rw [CarrierGeometryCongruence.nodeTime L K hb hT k p]
  · have h':=mt he.mpr h
    simp only [PhysicalScoreChain.direction,h,h',ite_false]

theorem directions (Z : Fin N→Observation) (k : ℕ) (p : History X k) :
    PhysicalChainArrays.directions L Z k p=PhysicalChainArrays.directions K Z k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    exact Fin.cases (direction L K hb hT Z k p) (fun j=>congrFun (ih p.1) j) i

theorem covariances (Z : Fin N→Observation) (c : Domain→ℝ) (k : ℕ) (p : History X k) :
    PhysicalChainArrays.covariances L Z c k p=PhysicalChainArrays.covariances K Z c k p := by
  unfold PhysicalChainArrays.covariances
  rw [lower L K hb hT k p,upper L K hb hT k p]

theorem scoreProduct (Z : Fin N→Observation) (c : Domain→ℝ) (k : ℕ) (p : History X k) :
    PhysicalScoreChain.scoreProduct L Z c k p=PhysicalScoreChain.scoreProduct K Z c k p := by
  unfold PhysicalScoreChain.scoreProduct
  rw [covariances L K hb hT Z c k p,directions L K hb hT Z k p]

theorem strict_iff (k : ℕ) (p : History X k) : StrictHistory L k p↔StrictHistory K k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact and_congr (ih p.1) (CarrierGeometryCongruence.interior_iff L K hb hT k p)

include hZ in
theorem small_iff (H : ℕ→ℝ) (k : ℕ) (p : History X k) :
    SmallHistory L H k p↔SmallHistory K H k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [SmallHistory,ih p.1,CarrierGeometryCongruence.observations L K hb hT hZ k p.1,
      CarrierGeometryCongruence.nodeTime L K hb hT k p]

theorem timeWeight (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (p : History X k) :
    PhysicalScoreChain.timeWeight L ell C k p=PhysicalScoreChain.timeWeight K ell C k p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [PhysicalScoreChain.timeWeight,ih p.1,
      CarrierGeometryCongruence.terminal L K hb hT k p.1,CarrierGeometryCongruence.nodeTime L K hb hT k p]

end SHE.CarrierPhysicalCongruence
