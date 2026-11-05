module

public import SHE.ShiftedWordGeometry
public import SHE.WeightedMeanKernel
public import SHE.WeightedRowTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.ShiftedWordCalculus
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry GaussianConvolution CutoffInsertionCore
variable {X : Type} [MeasurableSpace X] {R Q : ReferenceData} {n : ℕ}
variable (L : Level R X n) (K : Level Q X n) (v : ℝ)
variable (hb : Q.base=R.base+v)
variable (hT : ∀ x,K.terminal x=L.terminal x+v)
variable (hZ : ∀ x,K.observations.observations x=ObservationTimeShift.observations v (L.observations.observations x))
variable (hc : Q.reference=ObservationTimeShift.profile v R.reference)
include hb hT hZ hc

/-- Actual Gaussian node covariances are preserved by the full physical
history translation, including collided and inactive configurations. -/
theorem nodeCovariance_shift (k : ℕ) (p : History X (k+1)) :
    ((carrier K k).nodeCovariance (shift v (k+1) p)).val=((carrier L k).nodeCovariance p).val := by
  change covariance Q.reference ((carrier K k).observations.observations (shift v k p.1))
    ((carrier K k).nodeTime (shift v (k+1) p)) ((carrier K k).terminal (shift v k p.1))=_
  rw [hc,observations_shift L K v hb hT hZ k p.1,nodeTime_shift L K v hb hT k p,
    terminal_shift L K v hb hT k p.1]
  exact ObservationTimeShift.covariance_translation _ _ _ _ _

theorem covariance_shift (k : ℕ) (p : History X k) (q : ℝ) :
    covariance Q.reference ((carrier K k).observations.observations (shift v k p))
      (q+v) ((carrier K k).terminal (shift v k p))=
    covariance R.reference ((carrier L k).observations.observations p) q ((carrier L k).terminal p) := by
  rw [hc,observations_shift L K v hb hT hZ k p,terminal_shift L K v hb hT k p]
  exact ObservationTimeShift.covariance_translation _ _ _ _ _

variable (hV : Q.totalVariance=R.totalVariance) (hF : ∀ x,K.test x=L.test x)
include hV hF

/-- Every actual recursive insertion is preserved, not just its
Gaussian moment bound or its geometric envelope. -/
theorem test_shift (k : ℕ) (p : History X k) :
    UncutSmoothWords.test K k (shift v k p)=UncutSmoothWords.test L k p := by
  induction k with
  | zero=>exact hF p
  | succ k ih=>
    change core Q.totalVariance (Q.reference ((carrier K k).nodeTime (shift v (k+1) p),p.2.2))
      (CutoffCarriers.row K k (shift v (k+1) p))
      (gaussianAverage ((carrier K k).nodeCovariance (shift v (k+1) p)).val
        (UncutSmoothWords.test K k (shift v k p.1)))=_
    rw [hV,row_shift L K v hb hT hZ k p,nodeCovariance_shift L K v hb hT hZ hc k p,ih p.1,
      nodeTime_shift L K v hb hT k p,hc]
    change core _ (R.reference (((carrier L k).nodeTime p+v)-v,p.2.2)) _ _=_
    rw [add_sub_cancel_right]
    rfl

theorem cappedAverage_shift (k : ℕ) (p : History X k) (q : ℝ) :
    ActualMeanKernel.cappedAverage K k (q+v) (shift v k p)=ActualMeanKernel.cappedAverage L k q p := by
  unfold ActualMeanKernel.cappedAverage
  rw [terminal_shift L K v hb hT k p,min_add_add_right,hc,observations_shift L K v hb hT hZ k p,
    test_shift L K v hb hT hZ hc hV hF k p,ObservationTimeShift.covariance_translation]

/-- The true stop-weighted terminal derivative keeps its q-law, its
independent r-row, and its original finite recursive test under the
moving-past clock change. -/
theorem weightedPoint_shift (k : ℕ) (Λ q r : ℝ)
    (m : History X k→WordRecursion.State (n+k)) (p : History X k) (y : HeatCircle) :
    ActualMeanKernel.weightedPoint K k Λ (q+v) (r+v) m (shift v k p) y=
      ActualMeanKernel.weightedPoint L k Λ q r (fun p=>m (shift v k p)) p y := by
  classical
  unfold ActualMeanKernel.weightedPoint
  rw [terminal_shift L K v hb hT k p]
  simp only [add_lt_add_iff_right]
  split_ifs with ha
  · have hcov:=covariance_shift L K v hb hT hZ hc k p q
    rw [terminal_shift L K v hb hT k p] at hcov
    rw [hcov,test_shift L K v hb hT hZ hc hV hF k p,
      observations_shift L K v hb hT hZ k p,ObservationTimeShift.weightedHeatRow_translation]
  · rfl
end SHE.ShiftedWordCalculus
