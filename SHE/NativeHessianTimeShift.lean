module
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.ShiftedWordCalculus
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry GaussianConvolution
variable {X:Type}[MeasurableSpace X]{R Q:ReferenceData}{n:ℕ}
variable (L:Level R X n)(K:Level Q X n)(v:ℝ)
variable (hb:Q.base=R.base+v)(hT:∀x,K.terminal x=L.terminal x+v)
variable (hZ:∀x,K.observations.observations x=ObservationTimeShift.observations v (L.observations.observations x))
variable (hc:Q.reference=ObservationTimeShift.profile v R.reference)
variable (hV:Q.totalVariance=R.totalVariance)(hF:∀x,K.test x=L.test x)

include hb hT hZ hc hV hF in
/-- Full Gaussian backward words translate before differentiation; the
true original covariance and all old baselines are retained. -/
theorem average_shift(k:ℕ)(q:ℝ)(p:History X k):
    gaussianAverage (covariance Q.reference ((carrier K k).observations.observations (shift v k p))
      (q+v) ((carrier K k).terminal (shift v k p))) (UncutSmoothWords.test K k (shift v k p))=
    gaussianAverage (covariance R.reference ((carrier L k).observations.observations p)
      q ((carrier L k).terminal p)) (UncutSmoothWords.test L k p):=by
  rw [covariance_shift L K v hb hT hZ hc k p q,test_shift L K v hb hT hZ hc hV hF k p]

include hb hT hZ hc hV hF in
/-- Literal two-row Hessian translation, without a score representation
or a replacement of the law at the physical current. -/
theorem directionalSecond_shift(k:ℕ)(q:ℝ)(p:History X k)(m:WordRecursion.State (n+k))(y:HeatCircle):
    WordRecursion.directionalSecond
      (gaussianAverage (covariance Q.reference ((carrier K k).observations.observations (shift v k p))
        (q+v) ((carrier K k).terminal (shift v k p))) (UncutSmoothWords.test K k (shift v k p))) m
      (heatRow ((carrier K k).observations.observations (shift v k p)) (q+v) y)=
    WordRecursion.directionalSecond
      (gaussianAverage (covariance R.reference ((carrier L k).observations.observations p)
        q ((carrier L k).terminal p)) (UncutSmoothWords.test L k p)) m
      (heatRow ((carrier L k).observations.observations p) q y):=by
  rw [average_shift L K v hb hT hZ hc hV hF k q p,
    observations_shift L K v hb hT hZ k p,ObservationTimeShift.heatRow_translation]

end SHE.ShiftedWordCalculus
