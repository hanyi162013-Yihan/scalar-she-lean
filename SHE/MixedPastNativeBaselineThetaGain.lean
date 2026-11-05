module
public import SHE.MixedPastBaselineThetaSections
public import SHE.NativeOmittedTimeGain

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastNativeScoreEnergy
public import SHE.NativePastAgeScoreEnergy
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastNativeBaselineThetaGain
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

attribute [local irreducible] NativeOmittedTimeTotal.total MixedPastWordMoments.total MixedPastBaselineThetaRMS.amplitude

local notation "InputAmp"=>MixedPastBaselineThetaRMS.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v

def amplitude (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(j0:Fin k)(A0 ν:ℝ)(x:HeatCircle):ℝ:=
  let a:=anchor k t
  let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
  NativeOmittedTimeTotal.total (d:=1) P
    (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age j0 A0 ν*
    InputAmp (age j0) (x+w j0)

include hIJ₀ hIJ₁ in
/-- The actual theta-averaged derivative RMS restores the FULL erased
leaf age. Only a single ORIGINAL PAST quarter-power remains, uniformly
in the old relative spatial coordinates and the current time. -/
theorem actual_energy (hΛ:0≤Λ)
    (hsmallPoint:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H)(hv1:(v:ℝ)≤1)(Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)(k:ℕ):
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let a:=anchor k t
      ∀hp:StrictHistory Zero k a,∀q:ℝ≥0,v<q→(q:ℝ)<(carrier Zero k).terminal a→
      ∀w:Fin k→HeatCircle,∀j0:Fin k,∀A0 ν:ℝ,
      let age:=fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age A0 ν
      let A:=amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k t w j0 A0 ν
      Integrable (fun x=>A x^2) haarAddCircle ∧
        (∫x,A x^2 ∂haarAddCircle)≤
          (BaselineOriginalGain.unitCoefficient P*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ))*sharp)^2*
            (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  have hs:=MixedPastBaselineThetaSections.time_sections
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁
    P hΛ hsmallPoint hsmallL2 rfl v hvH hv1 1 (by decide) Bpast hBDGpast
    (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) 1 Zero (b:ℝ) (fun _=>rfl) le_rfl k
  filter_upwards [hs] with t ht
  intro a hp q hvq hqt w j0 A0 ν age sharp A
  let c:=NativeOmittedTimeTotal.total (d:=1) P
    (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age j0 A0 ν
  let D:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
  have hD:0≤D:=integral_nonneg (fun _=>sq_nonneg _)
  have hqv:0<(q:ℝ)-(v:ℝ):=sub_pos.mpr (by exact_mod_cast hvq)
  have hage:(q:ℝ)-(v:ℝ)≤age j0:=sub_le_sub_right
    (carrier_targets_after Zero a hages hqt (leafIndex k (fun i=>i) j0)).le _
  have hi:=ht hp j0
  have hit0:=(measurePreserving_add_right haarAddCircle (w j0)).integrable_comp_of_integrable hi.1
  have hit:Integrable (fun x:HeatCircle=>InputAmp (age j0) (x+w j0)^2) haarAddCircle:=by
    convert! hit0 using 1
  have hc:0≤c:=NativeOmittedTimeTotal.total_nonneg P _ _ _ _ _ _
  have hA:(fun x:HeatCircle=>A x^2)=(fun x=>c^2*InputAmp (age j0) (x+w j0)^2):=by
    funext x
    dsimp only [A,amplitude,c,age,a]
    ring
  have hai:Integrable (fun x=>A x^2) haarAddCircle:=by
    rw [hA]
    exact hit.const_mul _
  refine ⟨hai,?_⟩
  rw [hA,integral_const_mul,integral_add_right_eq_self (μ:=haarAddCircle) (fun x:HeatCircle=>InputAmp (age j0) x^2) (w j0)]
  have hbound:=NativeOmittedTimeTotal.restored_total_unit_gain (d:=1) P
    (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ)) age j0 A0 ν hqv hage
  have hsu:0≤ControlledProfile.sharpUnit P:=by
    unfold ControlledProfile.sharpUnit
    exact mul_nonneg (by norm_num) (meanConstant_nonneg P.lower_pos.le P.holder_nonneg)
  have hbase:0≤ControlledProfile.sharpUnit P*(age j0)^((P.exponent-1)/4)*c:=
    mul_nonneg (mul_nonneg hsu (Real.rpow_nonneg (hqv.le.trans hage) _)) hc
  calc
    _≤c^2*((ControlledProfile.sharpUnit P*(age j0)^((P.exponent-1)/4))^2*D):=
      mul_le_mul_of_nonneg_left hi.2 (sq_nonneg _)
    _=(ControlledProfile.sharpUnit P*(age j0)^((P.exponent-1)/4)*c)^2*D:=by ring
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase hbound 2) hD

end SHE.MixedPastNativeBaselineThetaGain
