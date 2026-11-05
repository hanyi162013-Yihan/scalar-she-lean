module

public import SHE.CarrierGeometryCongruence
public import SHE.ObservationTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.ShiftedWordGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
variable {X : Type} [MeasurableSpace X]

/-- Translate every genuine old time, preserving its original spatial
coordinate and its position in the recursive history. -/
def shift (v : ℝ) : (k : ℕ)→History X k→History X k
  | 0=>id
  | k+1=>fun p=>(shift v k p.1,(p.2.1+v,p.2.2))

theorem shift_joint_measurable (k : ℕ) : Measurable (fun z : ℝ×History X k=>shift z.1 k z.2) := by
  induction k with
  | zero=>exact measurable_snd
  | succ k ih=>
    exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      ((measurable_snd.snd.fst.add measurable_fst).prodMk measurable_snd.snd.snd)

theorem clip_add (a b t v : ℝ) :
    ClippedCovariance.clip (a+v) (b+v) (t+v)=ClippedCovariance.clip a b t+v := by
  simp only [ClippedCovariance.clip,min_add_add_right,max_add_add_right]

variable {R Q : ReferenceData} {n : ℕ} (L : Level R X n) (K : Level Q X n) (v : ℝ)
variable (hb : Q.base=R.base+v)
variable (hT : ∀ x,K.terminal x=L.terminal x+v)
variable (hZ : ∀ x,K.observations.observations x=ObservationTimeShift.observations v (L.observations.observations x))
include hb hT

theorem terminal_shift (k : ℕ) (p : History X k) :
    (carrier K k).terminal (shift v k p)=(carrier L k).terminal p+v := by
  induction k with
  | zero=>exact hT p
  | succ k ih=>
    change ClippedCovariance.clip Q.base ((carrier K k).terminal (shift v k p.1)) (p.2.1+v)=_
    rw [hb,ih p.1]
    exact clip_add _ _ _ _

theorem nodeTime_shift (k : ℕ) (p : History X (k+1)) :
    (carrier K k).nodeTime (shift v (k+1) p)=(carrier L k).nodeTime p+v := by
  change ClippedCovariance.clip Q.base ((carrier K k).terminal (shift v k p.1)) (p.2.1+v)=_
  rw [hb,terminal_shift L K v hb hT k p.1]
  exact clip_add _ _ _ _

include hZ in
theorem observations_shift (k : ℕ) (p : History X k) :
    (carrier K k).observations.observations (shift v k p)=
      ObservationTimeShift.observations v ((carrier L k).observations.observations p) := by
  induction k with
  | zero=>exact hZ p
  | succ k ih=>
    funext i
    refine Fin.cases ?_ (fun j=>congrFun (ih p.1) j) i
    change Observation.mk ((carrier K k).nodeTime (shift v (k+1) p))
      ((carrier K k).nodeTime (shift v (k+1) p)+0) p.2.2=
      Observation.mk ((carrier L k).nodeTime p+v) (((carrier L k).nodeTime p+0)+v) p.2.2
    rw [nodeTime_shift L K v hb hT k p]
    simp only [add_zero]

theorem interior_shift (k : ℕ) (p : History X (k+1)) :
    Interior K k (shift v (k+1) p)↔Interior L k p := by
  change (Q.base<p.2.1+v ∧ p.2.1+v<(carrier K k).terminal (shift v k p.1))↔_
  rw [hb,terminal_shift L K v hb hT k p.1]
  simp only [add_lt_add_iff_right]
  rfl

include hZ in
theorem row_shift (k : ℕ) (p : History X (k+1)) :
    CutoffCarriers.row K k (shift v (k+1) p)=CutoffCarriers.row L k p := by
  classical
  have hh:=interior_shift L K v hb hT k p
  by_cases hp : Interior L k p
  · have hp':=hh.mpr hp
    simp only [CutoffCarriers.row,if_pos hp,if_pos hp']
    change heatRow ((carrier K k).observations.observations (shift v k p.1))
      ((carrier K k).nodeTime (shift v (k+1) p)) p.2.2=_
    rw [observations_shift L K v hb hT hZ k p.1,nodeTime_shift L K v hb hT k p]
    exact ObservationTimeShift.heatRow_translation _ _ _ _
  · have hp':=mt hh.mp hp
    simp only [CutoffCarriers.row,if_neg hp,if_neg hp']

end SHE.ShiftedWordGeometry
