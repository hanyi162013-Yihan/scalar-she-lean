module

public import SHE.RootOldAverageSums
public import SHE.BoundedOldAverage
public import SHE.FiniteCovarianceSums
public import SHE.ActualCovarianceMarkFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.RootFiniteSums
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  SmoothCylinders UniformSmooth PhysicalScoreChain PhysicalChainArrays RootSmoothSums GaussianConvolution CoveredControlledLaw
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)
attribute [local irreducible] PhysicalChainArrays.oldAverage
  PhysicalChainArrays.fullResidualCovariance FiniteWordScores.covarianceMark
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse

theorem covariance_point_withRoot (G : X→WordRecursion.State n→ℝ) (hG : UniformBoundedSmooth G)
    (hGm : Measurable (fun z : X×WordRecursion.State n=>G z.1 z.2))
    (c e : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (q : ℝ)
    (m : WordRecursion.State (n+k)) (p : History X k) :
    ActualCovarianceMarkFields.point (withRoot L G hG hGm) c e k q m p=
      if q<(carrier L k).terminal p then
        FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
          (fullResidualCovariance L c k p q) e
          (StoppedGaussianFeatures.stoppedRow (stops L k p) (targets L k p) (centers L k p))
          (oldAverage (withRoot L G hG hGm) c k p) m else 0 := by
  unfold ActualCovarianceMarkFields.point
  rw [RootFiniteGeometry.terminal_eq L G hG hGm k p,RootPhysicalGeometry.fullResidual_eq L G hG hGm,
    RootFiniteGeometry.stops_eq L G hG hGm,RootFiniteGeometry.targets_eq L G hG hGm,
    RootFiniteGeometry.centers_eq L G hG hGm]

variable (F : ℕ→X→WordRecursion.State n→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
  (hFm : ∀ j,Measurable (fun z : X×WordRecursion.State n=>F j z.1 z.2))
local notation "B"=>band L F hF hFm
local notation "S"=>sumLevel L F hF hFm

/-- Actual full covariance marks are additive in literal finite root
cutoffs. The only physical applicability conditions are the ordinary
PSD/range/row-energy conditions for this signed continuum integral;
all old-Gaussian and root-word integral exchanges are derived. -/
theorem covariance_point_sum (s : Finset ℕ) (c e : StoppedGaussianFeatures.Domain→ℝ)
    (hc : Measurable c) (he : Measurable e) (k : ℕ) (q : ℝ)
    (m : WordRecursion.State (n+k)) (p : History X k)
    (hA : (fullResidualCovariance L c k p q).PosSemidef)
    (hr : Measurable (StoppedGaussianFeatures.stoppedRow (stops L k p) (targets L k p) (centers L k p)))
    (hrange : ∀ᵐ z ∂StoppedGaussianFeatures.historyMeasure q,
      StoppedGaussianFeatures.stoppedRow (stops L k p) (targets L k p) (centers L k p) z∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range)
    (henergy : Integrable (fun z=>|e z| *
      ‖StoppedGaussianFeatures.stoppedRow (stops L k p) (targets L k p) (centers L k p) z‖^2)
      (StoppedGaussianFeatures.historyMeasure q)) :
    ActualCovarianceMarkFields.point (S s) c e k q m p=
      ∑ j∈s,ActualCovarianceMarkFields.point (B j) c e k q m p := by
  classical
  simp only [sumLevel,band,covariance_point_withRoot L]
  by_cases hq : q<(carrier L k).terminal p
  · simp only [if_pos hq]
    change FiniteWordScores.covarianceMark _ _ e _ (oldAverage (S s) c k p) m=
      ∑ j∈s,FiniteWordScores.covarianceMark _ _ e _ (oldAverage (B j) c k p) m
    rw [oldAverage_sum L F hF hFm s c k p]
    have hf : (∑ j∈s,oldAverage (B j) c k p)=fun z=>∑ j∈s,oldAverage (B j) c k p z:=by
      funext z
      simp only [Finset.sum_apply]
    rw [hf]
    choose C hC hcb using fun j=>oldAverage_bounded (B j) c k p
    have hm (j : ℕ) : Measurable (oldAverage (B j) c k p):=
      (oldAverage_measurable (B j) c hc k).comp
        (measurable_const.prodMk (measurable_id : Measurable (id : WordRecursion.State (n+k)→_)))
    exact FiniteWordScores.covarianceMark_finset _ hA e he _ hr hrange henergy
      (fun j=>oldAverage (B j) c k p)
      hm
      C hcb s m
  · simp only [if_neg hq,Finset.sum_const_zero]
end SHE.RootFiniteSums
