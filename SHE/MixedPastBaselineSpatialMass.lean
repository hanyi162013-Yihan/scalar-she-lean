module

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastBaselineLeafMass
public import SHE.MixedPastBaselineSpatialEnergy
public import SHE.MixedPastBaselineLeafEnergy
public import SHE.MixedPastOmittedLeafAbsolute
public import SHE.FiniteSpatialBaseline
public import SHE.MixedPastBaselineFTCIdentity
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

namespace SHE.MixedPastBaselineSpatialMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineSpatialMass_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineSpatialMass_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineSpatialMass_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineSpatialMass_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineSpatialMass_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineSpatialMass_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastBaselineSpatialMass_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineSpatialMass_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastBaselineSpatialMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

open MixedPastBaselineSpatialEnergy

include hIJ₀ hIJ₁ in
/-- Complete literal random-past baseline spatial energy. Absolute old
space integrability is proved BEFORE the finite leaf sum is exchanged
with integration. The full original word time gain and one quarter
fresh loss survive, including the exactly zero depth-zero baseline. -/
theorem spatial_mass (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
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
      ∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ))
        (fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
      let scale:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a
      let C:=∑ j0 : Fin k,sqrt (MixedPastOmittedWord.momentConstant P k k 1 j0
        ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent))
      let gain:=scale*BaselineOriginalGain.unitCoefficient P*sharp*
        ((carrier Zero k).terminal a-(q:ℝ))^(-(1/4:ℝ))
      let G:=relativeBaseline 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q t
      Integrable G ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) ∧
      (∫ z,|G z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)))≤
        C*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*gain*
          sqrt (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  have hT : ∀ x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hder:=MixedPastBaselineEnergySections.time_sections
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P hΛ hsmall hsmallL2
    hinit v hvH hv1 p hp B hBDG
  have hleaf:=MixedPastBaselineLeafMass.leaf_mass
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmall hsmallL2 hages hspan A hA hcenter
    hinit hvH hv1 p hp B hBDG
  filter_upwards [hder,hleaf] with θ hd he
  intro k
  have hde:=hd _ 1 Zero (b:ℝ) hT (show (v:ℝ)≤_ from le_rfl) k
  have hab:=MixedPastOmittedLeafAbsolute.joint_integrable_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmall hages hspan A hA hcenter k
  filter_upwards [hde,he k,hab] with t htder htleaf htab
  intro a q hvq hqH hqt hstrict hs hθ A0 ν hA0 hν hjet B0 hBDG0 sharp scale C gain G
  let Fi:=fun j0 : Fin k=>MixedPastOmittedLeafSpatial.relativeLeaf
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q t j0
  let coeff:=fun j0 : Fin k=>MixedPastOmittedWord.momentConstant P k k 1 j0
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
  have hFi (j0 : Fin k) : Measurable (Fi j0):=MixedPastOmittedLeafSpatial.relative_leaf_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k θ q t j0
  have hJoint (j0 : Fin k) : Integrable (Fi j0)
      ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) := by
    have hh:=htab q hvq hqH hqt hstrict hs θ hθ A0 ν hA0 hν hjet j0 B0 hBDG0 (htder hstrict j0).1
    exact hh
  have hMass (j0 : Fin k) :
      (∫ z,|Fi j0 z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)))≤
        sqrt (coeff j0)*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*gain*
          sqrt (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
    exact htleaf q hvq hqH hqt hstrict hs hθ A0 ν hA0 hν hjet j0 B0 hBDG0
  have heq (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) : G z=-(∑ j0,Fi j0 z) :=
    MixedPastBaselineFTCIdentity.active_baseline_eq_neg_sum
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k
      (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)) θ q hvq z.1.1
  have hj : Integrable G ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) := by
    have hh:=(integrable_finsetSum Finset.univ (fun j _=>hJoint j)).neg
    exact hh.congr (ae_of_all _ (fun z=>(heq z).symm))
  refine ⟨hj,?_⟩
  calc
    _≤∫ z,∑ j0,|Fi j0 z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle)):=by
      apply integral_mono hj.norm (integrable_finsetSum Finset.univ (fun j _=>(hJoint j).norm))
      intro z
      change |G z|≤∑ j0,|Fi j0 z|
      rw [heq,abs_neg]
      exact Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun j : Fin k=>Fi j z)
    _=∑ j0,(∫ z,|Fi j0 z| ∂(μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))):=
      integral_finsetSum _ (fun j _=>(hJoint j).norm)
    _≤∑ j0,sqrt (coeff j0)*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*gain*
        sqrt (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=Finset.sum_le_sum (fun j _=>hMass j)
    _=_:=by
      simp only [←Finset.sum_mul]
      rfl

end SHE.MixedPastBaselineSpatialMass
