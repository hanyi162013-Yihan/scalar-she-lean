module

public import SHE.CarrierGeometryCongruence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.WordRootReindex
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
open GaussianConvolution CutoffInsertionCore
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

def history (f : X→Y) : (k:ℕ)→History X k→History Y k
  | 0=>f
  | k+1=>fun p=>(history f k p.1,p.2)

theorem history_measurable (f:X→Y) (hf:Measurable f) (k:ℕ):Measurable (history f k):=by
  induction k with
  | zero=>exact hf
  | succ k ih=>exact (ih.comp measurable_fst).prodMk measurable_snd

variable {R Q : ReferenceData} {n:ℕ} (L:Level R Y n) (K:Level Q X n) (f:X→Y)
variable (hb:Q.base=R.base) (hT:∀x,K.terminal x=L.terminal (f x))
variable (hZ:∀x,K.observations.observations x=L.observations.observations (f x))
include hb hT

theorem terminal (k:ℕ) (p:History X k):
    (carrier K k).terminal p=(carrier L k).terminal (history f k p):=by
  induction k with
  | zero=>exact hT p
  | succ k ih=>
    change ClippedCovariance.clip Q.base ((carrier K k).terminal p.1) p.2.1=_
    rw [hb,ih p.1]
    rfl

theorem nodeTime (k:ℕ) (p:History X (k+1)):
    (carrier K k).nodeTime p=(carrier L k).nodeTime (history f (k+1) p):=by
  change ClippedCovariance.clip Q.base ((carrier K k).terminal p.1) p.2.1=_
  rw [hb,terminal L K f hb hT k p.1]
  rfl

include hZ in
theorem observations (k:ℕ) (p:History X k):
    (carrier K k).observations.observations p=(carrier L k).observations.observations (history f k p):=by
  induction k with
  | zero=>exact hZ p
  | succ k ih=>
    funext i
    refine Fin.cases ?_ (fun j=>congrFun (ih p.1) j) i
    change Observation.mk ((carrier K k).nodeTime p) ((carrier K k).nodeTime p+0) p.2.2=_
    rw [nodeTime L K f hb hT k p]
    rfl

theorem interior_iff (k:ℕ) (p:History X (k+1)):
    Interior K k p↔Interior L k (history f (k+1) p):=by
  change (Q.base<p.2.1 ∧ p.2.1<(carrier K k).terminal p.1)↔_
  rw [hb,terminal L K f hb hT k p.1]
  rfl

include hZ in
theorem row (k:ℕ) (p:History X (k+1)):
    CutoffCarriers.row K k p=CutoffCarriers.row L k (history f (k+1) p):=by
  classical
  have he:=interior_iff L K f hb hT k p
  by_cases hp:Interior K k p
  · have hp':=he.mp hp
    simp only [CutoffCarriers.row,if_pos hp,if_pos hp']
    rw [observations L K f hb hT hZ k p.1,nodeTime L K f hb hT k p]
    rfl
  · have hp':=mt he.mpr hp
    simp only [CutoffCarriers.row,if_neg hp,if_neg hp']

variable (hc:Q.reference=R.reference) (hV:Q.totalVariance=R.totalVariance)
variable (hF:∀x,K.test x=L.test (f x))
include hZ hc hV hF

/-- Changing the reference horizon and the root parameter does not
change a literal recursive test when its physical data agree. -/
theorem test (k:ℕ) (p:History X k):
    UncutSmoothWords.test K k p=UncutSmoothWords.test L k (history f k p):=by
  induction k with
  | zero=>exact hF p
  | succ k ih=>
    have hcov:((carrier K k).nodeCovariance p).val=
        ((carrier L k).nodeCovariance (history f (k+1) p)).val:=by
      change covariance Q.reference ((carrier K k).observations.observations p.1)
        ((carrier K k).nodeTime p) ((carrier K k).terminal p.1)=_
      rw [hc,observations L K f hb hT hZ k p.1,nodeTime L K f hb hT k p,
        terminal L K f hb hT k p.1]
      rfl
    change core Q.totalVariance (Q.reference ((carrier K k).nodeTime p,p.2.2))
      (CutoffCarriers.row K k p) (gaussianAverage _ (UncutSmoothWords.test K k p.1))=_
    rw [hc,hV,nodeTime L K f hb hT k p,row L K f hb hT hZ k p,hcov,ih p.1]
    rfl

end SHE.WordRootReindex
