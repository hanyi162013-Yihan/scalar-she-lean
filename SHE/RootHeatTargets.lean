module

public import SHE.RootHeatBounds
public import SHE.CovarianceTargetContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.RootHeatTargets
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RootHeatBounds CovarianceTargetContinuity
open scoped NNReal
variable {P : Type*} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)

theorem target_continuous (k : ℕ) (p : History P k) (i : Fin (n+k)) :
    Continuous (fun ε : ℝ≥0 => ((level L δ hδ ε k).observations.observations p i).target) := by
  induction k with
  | zero =>
    change Continuous (fun ε : ℝ≥0 => (L.observations.observations p i).target+(ε:ℝ))
    exact continuous_const.add continuous_subtype_val
  | succ k ih =>
    change History P k × (ℝ × HeatCircle) at p
    refine Fin.cases ?_ (fun j => ih p.1 j) i
    change Continuous (fun ε : ℝ≥0 => (level L δ hδ ε k).nodeTime (p.1,p.2)+(ε:ℝ))
    have hc : Continuous (fun ε : ℝ≥0 => (level L δ hδ 0 k).nodeTime (p.1,p.2)+(ε:ℝ)) :=
      continuous_const.add continuous_subtype_val
    convert hc using 1
    funext ε
    rw [nodeTime_eq L δ hδ ε 0 k (p.1,p.2)]

theorem center_eq (ε η : ℝ≥0) (k : ℕ) (p : History P k) (i : Fin (n+k)) :
    ((level L δ hδ ε k).observations.observations p i).center=
      ((level L δ hδ η k).observations.observations p i).center := by
  induction k with
  | zero => rfl
  | succ k ih => exact Fin.cases rfl (fun j => ih p.1 j) i

theorem stop_eq (ε η : ℝ≥0) (k : ℕ) (p : History P k) (i : Fin (n+k)) :
    ((level L δ hδ ε k).observations.observations p i).stop=
      ((level L δ hδ η k).observations.observations p i).stop := by
  induction k with
  | zero => rfl
  | succ k ih => exact Fin.cases (nodeTime_eq L δ hδ ε η k p) (fun j => ih p.1 j) i

theorem good_iff (ε η : ℝ≥0) (k : ℕ) (p : History P k × (ℝ × HeatCircle)) :
    (level L δ hδ ε k).Good δ p ↔ (level L δ hδ η k).Good δ p := by
  unfold CutoffWordLevel.Level.Good
  rw [terminal_eq L δ hδ ε η k p.1]

theorem cutoffRow_continuous (k : ℕ) (p : History P k × (ℝ × HeatCircle)) :
    Continuous (fun ε : ℝ≥0 => (level L δ hδ ε k).cutoffRow δ p) := by
  classical
  by_cases hg : (level L δ hδ 0 k).Good δ p
  · have hge (ε : ℝ≥0) : (level L δ hδ ε k).Good δ p := (good_iff L δ hδ ε 0 k p).mpr hg
    have hnode : (level L δ hδ 0 k).nodeTime p=p.2.1 :=
      (level L δ hδ 0 k).nodeTime_eq hδ hg
    have he : (fun ε : ℝ≥0 => (level L δ hδ ε k).cutoffRow δ p)=
        fun ε => heatRow ((level L δ hδ ε k).observations.observations p.1)
          ((level L δ hδ 0 k).nodeTime p) p.2.2 := by
      funext ε
      rw [CutoffWordLevel.Level.cutoffRow,if_pos (hge ε),nodeTime_eq L δ hδ ε 0 k p]
    rw [he]
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+k) => ℝ)).comp
    apply continuous_pi
    intro i
    apply continuous_heatRow (fun ε => (level L δ hδ ε k).observations.observations p.1)
      (fun j => ((level L δ hδ 0 k).observations.observations p.1 j).center)
      (target_continuous L δ hδ k p.1) (fun ε j => center_eq L δ hδ ε 0 k p.1 j)
      (s := (level L δ hδ 0 k).nodeTime p+δ) (by linarith) ?_ p.2.2 i
    intro ε j
    rw [hnode]
    have hgood := (hge ε).2
    have htar := (level L δ hδ ε k).targets_after p.1 j
    linarith
  · have he : (fun ε : ℝ≥0 => (level L δ hδ ε k).cutoffRow δ p)=fun _ => 0 := by
      funext ε
      exact if_neg (fun hh => hg ((good_iff L δ hδ ε 0 k p).mp hh))
    rw [he]
    exact continuous_const

theorem nodeCovariance_continuous (k : ℕ) (p : History P k × (ℝ × HeatCircle)) :
    Continuous (fun ε : ℝ≥0 => (level L δ hδ ε k).nodeCovariance p) := by
  let q := (level L δ hδ 0 k).nodeTime p
  let s := (level L δ hδ 0 k).terminal p.1
  have hc := continuous_covariance R.reference R.reference_measurable
    (fun ε => (level L δ hδ ε k).observations.observations p.1)
    (fun i => ((level L δ hδ 0 k).observations.observations p.1 i).center)
    (target_continuous L δ hδ k p.1) (fun ε i => center_eq L δ hδ ε 0 k p.1 i)
    R.upper_nonneg ((level L δ hδ 0 k).nodeTime_mem p).2
    (fun ε i => by
      rw [← terminal_eq L δ hδ ε 0 k p.1]
      exact (level L δ hδ ε k).targets_after p.1 i)
    (fun _ _ _ => R.reference_bound _)
  apply Continuous.subtype_mk
  convert hc using 1
  funext ε
  change covariance R.reference ((level L δ hδ ε k).observations.observations p.1)
      ((level L δ hδ ε k).nodeTime p) ((level L δ hδ ε k).terminal p.1)=_
  rw [nodeTime_eq L δ hδ ε 0 k p,terminal_eq L δ hδ ε 0 k p.1]

end SHE.RootHeatTargets
