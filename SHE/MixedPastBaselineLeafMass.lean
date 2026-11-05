module

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastOmittedLeafMass
public import SHE.MixedPastOmittedLeafSpatial
public import SHE.MixedPastBaselineEnergySections
public import SHE.BaselineUnitGain
public import SHE.ForestLeafMarkEnergy
public import SHE.MixedPastOmittedLeafMoments
public import SHE.ScalarRootSharpSections
public import SHE.HistoryRelativeSections
public import SHE.MixedPastDerivativeRMS
public import SHE.MixedPastOmittedMarkFields
public import SHE.MixedPastLiteralOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
public import SHE.JointInterpolationFields
public import SHE.WeightedRowTimeShift
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 650000

namespace SHE.MixedPastBaselineLeafMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineLeafMass_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineLeafMass_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineLeafMass_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineLeafMass_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineLeafMass_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineLeafMass_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastBaselineLeafMass_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineLeafMass_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastBaselineLeafMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


open HistoryProductMeasure ScalarRootRelativeGeometry ProfileL2

include hIJ₀ hIJ₁ in
/-- Actual random-past baseline leaf energy with the ORIGINAL full
rough-leaf time gain restored. All native/conditional Gaussian input,
profile energy and old-space averaging applicability is discharged.
Only one fresh quarter power remains, with no depth-dependent loss. -/
theorem leaf_mass (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (A : ℝ) (hA : ∀ x i,(Z.observations x i).target=A)
    (hcenter : ∀ x i,(Z.observations x i).center=x)
    (hinit : v₀=u₀) (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    ∀ᵐ θ ∂volume,∀ k : ℕ,
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let a:=separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
      ∀ q : ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal a→
      ∀ hstrict : StrictHistory Zero k a,SmallHistory Zero (uniformHorizon 1) k a→
      |θ|≤1→∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)→
      ∀ j0 : Fin k,∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ))
        (fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
      let scale:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a
      let C:=MixedPastOmittedWord.momentConstant P k k 1 j0
        ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
      let gain:=scale*BaselineOriginalGain.unitCoefficient P*sharp*
        ((carrier Zero k).terminal a-(q:ℝ))^(-(1/4:ℝ))
      let G:=MixedPastOmittedLeafSpatial.relativeLeaf
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q t j0
      (∫ z,|G z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)))≤
        sqrt C*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*gain*
          sqrt (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  have hT : ∀ x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hder:=MixedPastBaselineEnergySections.time_sections
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P hΛ hsmall hsmallL2
    hinit v hvH hv1 p hp B hBDG
  filter_upwards [hder] with θ hθder
  intro k
  have hde:=hθder _ 1 Zero (b:ℝ) hT (show (v:ℝ)≤_ from le_rfl) k
  have hsp:=MixedPastOmittedLeafMass.mass_bound_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmall hages hspan A hA hcenter k
  filter_upwards [hde,hsp] with t htder htsp
  intro a q hvq hqH hqt hstrict hs hθ A0 ν hA0 hν hjet j0 B0 hBDG0 sharp scale C gain G
  let ages:=fun j : Fin k=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)
  let lo:=fun j=>lower Zero k a j-(v:ℝ)
  let hi:=fun j=>upper Zero k a j-(v:ℝ)
  let omitted:=MixedPastOmittedWord.total (d:=1) P lo hi ages j0 A0 ν
  have hinput:=htder hstrict j0
  have hbound:=htsp q hvq hqH hqt hstrict hs θ hθ A0 ν hA0 hν hjet j0 B0 hBDG0 hinput.1
  apply hbound.trans
  have hC : 0≤C:=MixedPastOmittedWord.momentConstant_nonneg _ _ _ _ _ _
  have hscale : 0≤scale:=timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos)
    (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k a hstrict
  have hU : 0≤ControlledProfile.sharpUnit P:=by
    rw [BaselineOriginalGain.sharpUnit_eq]
    exact mul_nonneg P.holder_nonneg (BaselineOriginalGain.unitCoefficient_nonneg P)
  have hgap : 0<(carrier Zero k).terminal a-(q:ℝ):=sub_pos.mpr hqt
  have hga : (carrier Zero k).terminal a-(q:ℝ)≤ages j0:=by
    have htleaf : targets Zero k a (leafIndex k (fun i=>i) j0)=lower Zero k a j0:=by
      rw [targets,leaf_observation Zero k a j0]
    dsimp only [ages]
    rw [htleaf]
    have hh:=terminal_le_lower Zero k a j0
    have hvq':(v:ℝ)≤(q:ℝ):=hvq
    linarith
  have hg:=MixedPastOmittedWord.restored_total_unit_gain (d:=1) P lo hi ages j0 A0 ν hgap hga
  have hO : 0≤omitted:=MixedPastOmittedWord.total_nonneg P lo hi ages j0 A0 ν
  have hEn : 0≤(∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=integral_nonneg (fun _=>sq_nonneg _)
  have hsqrt:=sqrt_le_sqrt hinput.2
  rw [sqrt_mul (sq_nonneg _),sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg hU (rpow_nonneg (hgap.le.trans hga) _))] at hsqrt
  have hcoeff : 0≤sqrt C*scale*omitted*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ):=
    mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) hscale) hO) (Nat.cast_nonneg _)
  have hm:=mul_le_mul_of_nonneg_left hsqrt hcoeff
  let cg:=sqrt C*scale*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*
    sqrt (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
  have hcg : 0≤cg:=mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg C) hscale)
    (Nat.cast_nonneg _)) (sqrt_nonneg _)
  have hmg:=mul_le_mul_of_nonneg_left hg hcg
  calc
    _≤sqrt C*scale*omitted*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*
        (ControlledProfile.sharpUnit P*(ages j0)^((P.exponent-1)/4)*
          sqrt (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ)):=hm
    _≤_:=by
      convert! hmg using 1 <;> dsimp only [gain,sharp,omitted,lo,hi,ages,cg] <;> ring

end SHE.MixedPastBaselineLeafMass
