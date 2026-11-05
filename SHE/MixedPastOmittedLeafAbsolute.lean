module

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastOmittedLeafSections
public import SHE.ForestLeafAbsolute
public import SHE.MixedPastOmittedLeafSpatial
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

namespace SHE.MixedPastOmittedLeafAbsolute
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOmittedLeafAbsolute_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOmittedLeafAbsolute_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOmittedLeafAbsolute_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOmittedLeafAbsolute_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOmittedLeafAbsolute_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOmittedLeafAbsolute_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastOmittedLeafAbsolute_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOmittedLeafAbsolute_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastOmittedLeafAbsolute_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

open MixedPastOmittedLeafSpatial

include hIJ₀ hIJ₁ in
/-- The literal actual omitted-baseline leaf is averaged in original
relative old space BEFORE sample/output L2. The derivative and native
word remain correlated throughout the conditional estimate. -/
theorem joint_integrable_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (A : ℝ) (hA : ∀ x i,(Z.observations x i).target=A)
    (hcenter : ∀ x i,(Z.observations x i).center=x) (k : ℕ) :
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let a:=separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
      ∀ q : ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal a→
      ∀ hp : StrictHistory Zero k a,SmallHistory Zero (uniformHorizon 1) k a→
      ∀ θ : ℝ,|θ|≤1→∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)→
      ∀ j0 : Fin k,∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      let age:=targets Zero k a (leafIndex k (fun i=>i) j0)-(v:ℝ)
      let e:=MixedPastDerivativeRMS.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v age θ
      Integrable (fun z : Ω×HeatCircle=>|e z|^2) (μ.prod haarAddCircle)→
      let G:=relativeLeaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q t j0
      Integrable G ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) := by
  have hp:=MixedPastOmittedLeafSections.point_energy_sections_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmall hages hspan A hA hcenter k
  filter_upwards [hp] with t ht
  intro a q hvq hqH hqt hp hs θ hθ A0 ν hA0 hν hjet j0 B0 hBDG age e hei G
  let sharp:=MixedPastOmittedWord.total (d:=1) P
    (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ))
    (fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)) j0 A0 ν
  let scale:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a
  let C:=MixedPastOmittedWord.momentConstant P k k 1 j0
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
  have hb:=ht q hvq hqH hqt hp hs θ hθ A0 ν hA0 hν hjet j0 B0 hBDG hei
  have hm:=MixedPastOmittedLeafSpatial.relative_leaf_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k θ q t j0
  have he:=MixedPastDerivativeRMS.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hΛ hsmall v age θ
  exact ForestLeafAbsolute.joint_integrable μ 2 (by norm_num) (targets Zero k a)
    (carrier_orderedTimes Zero hages k a hp) (fun _ : Fin 1=>(0:HeatCircle))
    (leafIndex k (fun i=>i) j0) e he hei G hm (C*(scale*sharp)^2)
    (mul_nonneg (MixedPastOmittedWord.momentConstant_nonneg _ _ _ _ _ _) (sq_nonneg _))
    (hb.mono (fun x hx=>hx.mono (fun w hw=>hw.1)))
    (hb.mono (fun x hx=>hx.mono (fun w hw=>hw.2)))

end SHE.MixedPastOmittedLeafAbsolute
