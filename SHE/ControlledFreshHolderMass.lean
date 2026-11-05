module
public import SHE.ControlledThetaSupported
public import SHE.PhysicalFreshMassChain

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.ControlledFreshHolderMass
open Set MeasureTheory ProbabilityTheory AddCircle GaussianAudit StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  ControlledProfile ControlledReferenceLevel ControlledReferenceWindows SmoothCylinders UniformSmooth
  GaussianConvolution ControlledFamilyProfileForest ControlledOldIntervals
open scoped BigOperators NNReal
local instance controlledFreshHolderMass_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledFreshHolderMass_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledFreshHolderMass_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
attribute [local irreducible] WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable (P:CanonicalCovariance.ProfileParameters)(ha:BoundedSmooth P.coefficient)
variable (Λ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {X:Type}[MeasurableSpace X](Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient ha Λ v b hvb Z htarget hstop F hF hFm

/-- ONE physical history event gives the derivative-free fresh Hölder
mass for every theta, every past-input pair, and every current mean.
Consequently random-past substitution needs no uncountable AE inference. -/
theorem all_parameters_ae {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient ha Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,0≤q→q<(carrier (Base p) k).terminal h→
        (carrier (Base p) k).terminal h-q≤1→∀z:WordRecursion.State (1+k),
      Integrable (fun x:HeatCircle=>WordRecursion.directionalSecond
        (gaussianAverage (WordRecursion.covariance
          (referenceData P P.coefficient ha Λ p.1 v b hvb p.2).reference
          ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
            (UncutSmoothWords.test (Base p) k h)) z
              (heatRow ((carrier (Base p) k).observations.observations h) q x)) haarAddCircle ∧
      (∫x:HeatCircle,|WordRecursion.directionalSecond
        (gaussianAverage (WordRecursion.covariance
          (referenceData P P.coefficient ha Λ p.1 v b hvb p.2).reference
          ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
            (UncutSmoothWords.test (Base p) k h)) z
              (heatRow ((carrier (Base p) k).observations.observations h) q x)| ∂haarAddCircle)≤
        ((2:ℝ)^k*scoreProduct (Base p) ((carrier (Base p) k).observations.observations h)
          (oldProfile P Λ v p.2) k h)*
          ((1+B+(P.upper+P.upper)/2)^(k+1)*secondScoreAbsIncrementMoment P.exponent*
            (Hr+(k:ℝ)*P.holder/2)*IntervalScoreHolderMass.constant (1+k) P.lower P.exponent*
              ((carrier (Base p) k).terminal h-q)^(P.exponent/4-1)) := by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
    P P.coefficient ha Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hs
  intro p q hq hqt hgap z
  obtain ⟨chain,hchain,_,hphysical⟩:=hs p
  have hc:Measurable (oldProfile P Λ v p.2):=
    (coefficient_section_measurable P Λ 0 v p.2).const_mul (fraction P)
  have hR(r:StoppedGaussianFeatures.Domain):P.lower≤
      (referenceData P P.coefficient ha Λ p.1 v b hvb p.2).reference r:=
    (coefficient_bounds P Λ p.1 v p.2 r).1
  have hcoef(z:ℝ):|P.coefficient z|≤P.upper:=by
    rw [abs_of_pos (P.lower_pos.trans_le (P.lower_bound z))]
    exact P.upper_bound z
  obtain ⟨hi,hbnd⟩:=hessian_holder_mass_of_chain (Base p) (oldProfile P Λ v p.2) hc
    P.lower_pos hR P.upper_nonneg hB P.holder_nonneg hHr P.exponent_pos.le
    (P.exponent_le_one.trans (by norm_num)) hcoef hroot P.holder_bound hrootmod hages
    k h chain hchain hphysical q hq hqt hgap z
  have hold:=old_absolute_mass_of_chain (Base p) (oldProfile P Λ v p.2) k h chain hphysical
  have hm:0≤secondScoreAbsIncrementMoment P.exponent:=integral_nonneg (fun _=>by positivity)
  have hIc:0≤IntervalScoreHolderMass.constant (1+k) P.lower P.exponent:=by
    unfold IntervalScoreHolderMass.constant
    have hhc:=StoppedFourier.heatConstant_pos
    have hl:=P.lower_pos
    positivity
  have hK:0≤(1+B+(P.upper+P.upper)/2)^(k+1)*secondScoreAbsIncrementMoment P.exponent*
      (Hr+(k:ℝ)*P.holder/2)*IntervalScoreHolderMass.constant (1+k) P.lower P.exponent*
        ((carrier (Base p) k).terminal h-q)^(P.exponent/4-1):=by
    have hu:=P.upper_nonneg
    have hh:=P.holder_nonneg
    positivity
  have hbnd':(∫x:HeatCircle,|WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance
        (referenceData P P.coefficient ha Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
          (UncutSmoothWords.test (Base p) k h)) z
            (heatRow ((carrier (Base p) k).observations.observations h) q x)| ∂haarAddCircle)≤
      oldAbsoluteMass (Base p) (oldProfile P Λ v p.2) k h*
        ((1+B+(P.upper+P.upper)/2)^(k+1)*secondScoreAbsIncrementMoment P.exponent*
          (Hr+(k:ℝ)*P.holder/2)*IntervalScoreHolderMass.constant (1+k) P.lower P.exponent*
            ((carrier (Base p) k).terminal h-q)^(P.exponent/4-1)):=by
    change _≤(1+B+(P.upper+P.upper)/2)^(k+1)*oldAbsoluteMass (Base p) (oldProfile P Λ v p.2) k h*
      secondScoreAbsIncrementMoment P.exponent*(Hr+(k:ℝ)*P.holder/2)*
        IntervalScoreHolderMass.constant (1+k) P.lower P.exponent*
          ((carrier (Base p) k).terminal h-q)^(P.exponent/4-1) at hbnd
    exact hbnd.trans_eq (by ring)
  exact ⟨hi,hbnd'.trans (mul_le_mul_of_nonneg_right hold hK)⟩

end SHE.ControlledFreshHolderMass
