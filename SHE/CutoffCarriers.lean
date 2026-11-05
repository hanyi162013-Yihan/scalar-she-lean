module

public import SHE.RecursiveHeatBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.CutoffCarriers
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open scoped NNReal
variable {P : Type*} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def carrier (k : ℕ) : CutoffWordLevel.Level R (History P k) (n+k) :=
  RecursiveHeatBounds.level L 1 zero_lt_one 0 k

theorem terminal_eq {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (k : ℕ) (p : History P k) :
    (RecursiveHeatBounds.level L δ hδ 0 k).terminal p=
      (RecursiveHeatBounds.level L η hη 0 k).terminal p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ClippedCovariance.clip R.base ((RecursiveHeatBounds.level L δ hδ 0 k).terminal p.1) p.2.1=
      ClippedCovariance.clip R.base ((RecursiveHeatBounds.level L η hη 0 k).terminal p.1) p.2.1
    rw [ih p.1]

theorem nodeTime_eq {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (k : ℕ)
    (p : History P k × (ℝ × HeatCircle)) :
    (RecursiveHeatBounds.level L δ hδ 0 k).nodeTime p=
      (RecursiveHeatBounds.level L η hη 0 k).nodeTime p := by
  change ClippedCovariance.clip R.base ((RecursiveHeatBounds.level L δ hδ 0 k).terminal p.1) p.2.1=
    ClippedCovariance.clip R.base ((RecursiveHeatBounds.level L η hη 0 k).terminal p.1) p.2.1
  rw [terminal_eq L hδ hη k p.1]

theorem observations_eq {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (k : ℕ) (p : History P k) :
    (RecursiveHeatBounds.level L δ hδ 0 k).observations.observations p=
      (RecursiveHeatBounds.level L η hη 0 k).observations.observations p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => congrFun (ih p.1) j) i
    change Observation.mk ((RecursiveHeatBounds.level L δ hδ 0 k).nodeTime p)
        ((RecursiveHeatBounds.level L δ hδ 0 k).nodeTime p+0) p.2.2=
      Observation.mk ((RecursiveHeatBounds.level L η hη 0 k).nodeTime p)
        ((RecursiveHeatBounds.level L η hη 0 k).nodeTime p+0) p.2.2
    rw [nodeTime_eq L hδ hη k p]

theorem nodeCovariance_eq {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (k : ℕ)
    (p : History P k × (ℝ × HeatCircle)) :
    (RecursiveHeatBounds.level L δ hδ 0 k).nodeCovariance p=
      (RecursiveHeatBounds.level L η hη 0 k).nodeCovariance p := by
  apply Subtype.ext
  change covariance R.reference ((RecursiveHeatBounds.level L δ hδ 0 k).observations.observations p.1)
      ((RecursiveHeatBounds.level L δ hδ 0 k).nodeTime p) ((RecursiveHeatBounds.level L δ hδ 0 k).terminal p.1)=_
  rw [observations_eq L hδ hη k p.1,nodeTime_eq L hδ hη k p,terminal_eq L hδ hη k p.1]
  rfl

theorem cutoffRow_eq {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (p : History P k × (ℝ × HeatCircle)) :
    (RecursiveHeatBounds.level L δ hδ 0 k).cutoffRow δ p=(carrier L k).cutoffRow δ p := by
  classical
  unfold CutoffWordLevel.Level.cutoffRow CutoffWordLevel.Level.Good
  rw [terminal_eq L hδ zero_lt_one k p.1]
  rw [observations_eq L hδ zero_lt_one k p.1,nodeTime_eq L hδ zero_lt_one k p]
  rfl

theorem test_succ {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (p : History P (k+1)) :
    (RecursiveHeatBounds.level L δ hδ 0 (k+1)).test p=
      CutoffInsertionCore.core R.totalVariance (R.reference ((carrier L k).nodeTime p,p.2.2))
        ((carrier L k).cutoffRow δ p)
        (GaussianConvolution.gaussianAverage ((carrier L k).nodeCovariance p).val
          ((RecursiveHeatBounds.level L δ hδ 0 k).test p.1)) := by
  change CutoffInsertionCore.core R.totalVariance
    (R.reference ((RecursiveHeatBounds.level L δ hδ 0 k).nodeTime p,p.2.2))
    ((RecursiveHeatBounds.level L δ hδ 0 k).cutoffRow δ p)
    (GaussianConvolution.gaussianAverage ((RecursiveHeatBounds.level L δ hδ 0 k).nodeCovariance p).val
      ((RecursiveHeatBounds.level L δ hδ 0 k).test p.1))=_
  rw [nodeTime_eq L hδ zero_lt_one k p,cutoffRow_eq L hδ k p,nodeCovariance_eq L hδ zero_lt_one k p]
  rfl

def Interior (k : ℕ) (p : History P k × (ℝ × HeatCircle)) : Prop :=
  R.base<p.2.1 ∧ p.2.1<(carrier L k).terminal p.1

theorem interior_measurableSet (k : ℕ) : MeasurableSet {p | Interior L k p} :=
  (measurableSet_lt measurable_const measurable_snd.fst).inter
    (measurableSet_lt measurable_snd.fst ((carrier L k).terminal_measurable.comp measurable_fst))

def row (k : ℕ) (p : History P k × (ℝ × HeatCircle)) : WordRecursion.State (n+k) := by
  classical
  exact if Interior L k p then heatRow ((carrier L k).observations.observations p.1)
    ((carrier L k).nodeTime p) p.2.2 else 0

theorem row_measurable (k : ℕ) : Measurable (row L k) := by
  classical
  have hp : Measurable (fun p : History P k × (ℝ × HeatCircle) =>
      (p.1,((carrier L k).nodeTime p,p.2.2))) :=
    measurable_fst.prodMk ((carrier L k).nodeTime_measurable.prodMk measurable_snd.snd)
  exact ((carrier L k).observations.heatRow_measurable.comp hp).ite
    (interior_measurableSet L k) measurable_const

end SHE.CutoffCarriers
