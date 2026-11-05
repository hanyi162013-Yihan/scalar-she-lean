module

public import SHE.PredictableScoreChain
public import SHE.UncutWordEvaluation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ProjectedUncutWord
open Set MeasureTheory ProbabilityTheory WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers GaussianCoordinates GaussianConvolution StoppedFourier
open scoped BigOperators
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable {L : CutoffWordLevel.Level R P n}

/-- The literal predictable reference term in the uncut finite expansion
has one residual Gaussian covariance and one fixed-old score average of
the original full root/leaf test. The initial-to-newest covariance and
the true initial heat mean are explicitly retained. -/
theorem Chain.reference_eq_reserved_average {k : ℕ} {p : History P k}
    (chain : Chain (N := n+k) L k p (fun i => i))
    (hs : chain.CoordinateSupport) (u : CircleL2) :
    UncutWordEvaluation.reference L u k p =
      gaussianAverage
        (((carrier L k).nodeCovariance (p,(R.base,0))).val + ∑ j, chain.residual j)
        chain.oldAverage
        (CanonicalConditional.initialMean ((carrier L k).observations.observations p) R.base u) := by
  have hp : projection (fun i : Fin (n+k) => i) =
      ContinuousLinearMap.id ℝ (WordRecursion.State (n+k)) := by
    ext z i
    rfl
  have h := chain.predictable_eq_reserved_average hs
    ((carrier L k).nodeCovariance (p,(R.base,0))).property
    (CanonicalConditional.initialMean ((carrier L k).observations.observations p) R.base u)
  simpa only [hp, ContinuousLinearMap.id_apply, UncutWordEvaluation.reference,
    gaussianAverage, GaussianSmooth.average] using h

end SHE.ProjectedUncutWord
