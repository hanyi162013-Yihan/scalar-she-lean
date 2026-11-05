module

public import SHE.BoundedThetaRelativeSecondScore
public import SHE.ControlledThetaPhysicalMarkFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.VariableFiniteMarkFields
public import SHE.ObservationMarkTimeShift
public import SHE.BoundedOldAverage
public import SHE.ControlledThetaRelativeArrays

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledFiniteCovarianceFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i, (b : ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i, (b : ℝ) ≤ (Z.observations x i).stop)
variable (F : X → WordRecursion.State 1 → ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X × WordRecursion.State 1 => F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0, (0, 0))
local notation "Cov" => BoundedThetaRelativeSecondScore.covariance P hA Λ v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
attribute [local irreducible] ControlledFamilyProfileForest.oldProfile PhysicalChainArrays.oldAverage
set_option backward.isDefEq.respectTransparency true

def point (p : ℝ×Inputs) (k : ℕ) (h : History X k) (q θ₀ θ₁ ζ : ℝ)
    (mean : WordRecursion.State (1+k)) : ℝ :=
  FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
    ((1-ζ) • ActualCovarianceMarkFields.cappedResidual (Base (θ₀,p.2)) (oldProfile P Λ v p.2) k h q+
      ζ • ActualCovarianceMarkFields.cappedResidual (Base (θ₁,p.2)) (oldProfile P Λ v p.2) k h q)
    (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₁,z)-
      ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₀,z)))
    (StoppedGaussianFeatures.stoppedRow (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h))
    (oldAverage (Base p) (oldProfile P Λ v p.2) k h) mean

local notation "Point"=>point P hA Λ v b hvb Z htarget hstop F hF hFm

/-- Joint Borel finite covariance leg for arbitrary dependent original
past inputs, endpoint parameters, histories and current means. The Borel
extension agrees with the original full residual through terminal time. -/
theorem point_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q θ₀ θ₁ ζ : W→ℝ) (hq : Measurable q) (hθ₀ : Measurable θ₀) (hθ₁ : Measurable θ₁)
    (hζ : Measurable ζ) (mean : W→WordRecursion.State (1+k)) (hm : Measurable mean) :
    Measurable (fun w=>Point (p w) k (h w) (q w) (θ₀ w) (θ₁ w) (ζ w) (mean w)) := by
  let a₀:=fun w=>(θ₀ w,(p w).2)
  let a₁:=fun w=>(θ₁ w,(p w).2)
  have ha₀ : Measurable a₀:=hθ₀.prodMk hp.snd
  have ha₁ : Measurable a₁:=hθ₁.prodMk hp.snd
  have hc:=ControlledFamilyProfileMarkFields.old_profile_variable_measurable P Λ v
    (fun w=>(p w).2) hp.snd
  have hB₀:=ControlledThetaCovarianceFields.capped_residual_variable_measurable
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k a₀ ha₀ h hh q hq _ hc
  have hB₁:=ControlledThetaCovarianceFields.capped_residual_variable_measurable
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k a₁ ha₁ h hh q hq _ hc
  have hB : Measurable (fun w=>
      (1-ζ w) • ActualCovarianceMarkFields.cappedResidual (Base (a₀ w))
        (oldProfile P Λ v (p w).2) k (h w) (q w)+
      ζ w • ActualCovarianceMarkFields.cappedResidual (Base (a₁ w))
        (oldProfile P Λ v (p w).2) k (h w) (q w)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_const.sub hζ).mul
      (measurable_pi_iff.mp (measurable_pi_iff.mp hB₀ i) j)).add
        (hζ.mul (measurable_pi_iff.mp (measurable_pi_iff.mp hB₁ i) j))
  have hc' : Measurable (fun z : (W×WordRecursion.State (1+k))×StoppedGaussianFeatures.Domain=>
      oldProfile P Λ v (p z.1.1).2 z.2) :=
    hc.comp (measurable_fst.fst.prodMk measurable_snd)
  have hW:=ControlledThetaOldAverageFields.old_average_variable_measurable
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : W×WordRecursion.State (1+k)=>p z.1) (hp.comp measurable_fst)
    (fun z=>h z.1) (hh.comp measurable_fst)
    (fun z=>oldProfile P Λ v (p z.1.1).2 z.2)
    hc' Prod.snd measurable_snd
  have hcoeff:=ControlledThetaWordFields.coefficient_joint_measurable P Λ v
  have hc₀:=hcoeff.comp ((ha₀.comp measurable_fst).prodMk measurable_snd)
  have hc₁:=hcoeff.comp ((ha₁.comp measurable_fst).prodMk measurable_snd)
  have he:=hc₁.sub hc₀
  let S:=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun w=>(p w,h w)) (hp.prodMk hh)
  let ZB : VariableObservations.Family W (1+k) :=
    { observations:=fun w i=>⟨min (S.observations w i).stop (b:ℝ),
        (S.observations w i).target,(S.observations w i).center⟩
      stop_measurable:=fun i=>(S.stop_measurable i).min measurable_const
      target_measurable:=S.target_measurable
      center_measurable:=S.center_measurable }
  have hrow : Measurable (fun z : W×StoppedGaussianFeatures.Domain=>StoppedGaussianFeatures.stoppedRow
      (stops (Base (p z.1)) k (h z.1)) (targets (Base (p z.1)) k (h z.1))
      (centers (Base (p z.1)) k (h z.1)) z.2) := by
    convert StoppedGaussianFields.row_measurable ZB using 1
    rfl
  have hpoint:=VariableFiniteMarkFields.history_covariance_mark_measurable
    (fun w=>(1-ζ w) • ActualCovarianceMarkFields.cappedResidual (Base (a₀ w))
      (oldProfile P Λ v (p w).2) k (h w) (q w)+
      ζ w • ActualCovarianceMarkFields.cappedResidual (Base (a₁ w))
      (oldProfile P Λ v (p w).2) k (h w) (q w)) hB
    (fun z=>oldAverage (Base (p z.1)) (oldProfile P Λ v (p z.1).2) k (h z.1) z.2) hW
    mean hm _ hrow _ he q hq
  exact hpoint

/-- The extension uses the ORIGINAL terminal covariance at q=terminal;
only values outside the physical window are capped. -/
theorem point_of_window (p : ℝ×Inputs) (k : ℕ) (h : History X k) (q : ℝ)
    (hq : q≤(carrier Zero k).terminal h) (θ₀ θ₁ ζ : ℝ) (mean : WordRecursion.State (1+k)) :
    Point p k h q θ₀ θ₁ ζ mean=
      FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
        ((1-ζ) • fullResidualCovariance (Base (θ₀,p.2)) (oldProfile P Λ v p.2) k h q+
          ζ • fullResidualCovariance (Base (θ₁,p.2)) (oldProfile P Λ v p.2) k h q)
        (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₁,z)-
          ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₀,z)))
        (StoppedGaussianFeatures.stoppedRow (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h))
        (oldAverage (Base p) (oldProfile P Λ v p.2) k h) mean := by
  have ht (a : ℝ) : q≤(carrier (Base (a,p.2)) k).terminal h := by
    rwa [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm (a,p.2) (0,(0,0)) k h]
  simp only [point,ActualCovarianceMarkFields.cappedResidual,min_eq_left (ht θ₀),min_eq_left (ht θ₁)]

end SHE.ControlledFiniteCovarianceFields
