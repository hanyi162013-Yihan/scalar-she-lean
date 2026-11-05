module
public import SHE.FullOrdinaryHeatBandError
public import SHE.HilbertFiniteEnergy
public import SHE.FiniteOrdinaryErrorDiagonal
public import SHE.FullOrdinaryErrorOutput
public import SHE.ScalarHeatBandHolder
public import SHE.MixedFirstDefectActualBound
public import SHE.ScalarHeatRootBands
public import SHE.JointGammaRootHilbertPair
public import SHE.MixedFirstDefectNativeBound
public import SHE.MixedFirstDefectEnvelopeIdentity

public import SHE.MixedFirstDefectNormEnvelope
public import SHE.MixedFirstDefectConvolutionTransport
public import SHE.MixedFirstDefectMinkowski
public import SHE.MixedFirstDefectDisintegration
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectIntegral
public import SHE.MixedJointActiveVolume
public import SHE.MixedFirstDefectRMS
public import SHE.ControlledReferenceFamilyDefectL1
public import SHE.RootHistoryCurrentMeasure
public import SHE.NativeBesselParameterAverageAE
public import SHE.HistoryMeasureGeometry
public import SHE.MixedCanonicalRootFields
public import SHE.DefectRelativeFactor
public import SHE.DefectCombinedTime
public import SHE.NativeBesselFieldAE
public import SHE.NativeSignedHaarProcess
public import SHE.ControlledScalarReference
public import SHE.ControlledThetaDefectEnvelope
public import SHE.MixedJointUncutDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.FullOrdinaryFiniteBandError
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw
open scoped NNReal ENNReal BigOperators
open Classical
local instance mixedFirstDefectRMS_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedFirstDefectRMS_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedFirstDefectRMS_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedFirstDefectRMS_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a)
local notation "Family"=>ControlledScalarReference.observations b
local notation "Root" j:max=>(fun z:WordRecursion.State 1=>ScalarHeatBands.band a (j+1) (z 0))
local notation "RootSmooth" j:max=>(ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right (EuclideanSpace.proj (0:Fin 1))
local notation "RootFamily" j:max=>(fun _:HeatCircle=>Root j)
local notation "RootUniform" j:max=>UniformSmooth.UniformBoundedSmooth.fixed (P:=HeatCircle) (RootSmooth j)
local notation "RootMeasurable" j:max=>(RootSmooth j).smooth.continuous.measurable.comp
  (measurable_snd:Measurable (Prod.snd:HeatCircle×WordRecursion.State 1→WordRecursion.State 1))
local notation "JT" j:max=>MixedCanonicalRootHilbertExpansion.term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs 1 v b hvb Family (JointGammaRootHilbertPair.scalarTargetBound b) (JointGammaRootHilbertPair.scalarStopBound b)
    (RootFamily j) (RootUniform j) (RootMeasurable j)


open FiniteHaar
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (haP:SmoothCylinders.BoundedSmooth P.coefficient)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)


local notation "Val"=>FullOrdinaryHeatBandError.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP

def bandBudget (Q:CanonicalCovariance.ProfileParameters)(κ M H Λ ρ B K β:ℝ)
    (depth:ℕ)(B0:ℕ→ℝ≥0)(j:ℕ):ℝ:=
  H*Λ^(-ρ)*MixedPastNewestFiniteError.constant Q κ M 0 1 (2*B) (2*K) depth B0
    (ScalarHeatBandBernstein.amplitude B K β depth*((2:ℝ)^(j+1))^(-β)) ((2:ℝ)^(j+1))

def budget (Q:CanonicalCovariance.ProfileParameters)(κ M H Λ ρ B K β:ℝ)
    (depth:ℕ)(B0:ℕ→ℝ≥0)(s:Finset ℕ):ℝ:=
  (s.card:ℝ)*∑j∈s,bandBudget Q κ M H Λ ρ B K β depth B0 j

include hsmall hIJ₀ hIJ₁ hnull hJ hAs in
/-- A full retained finite-frequency ordinary approximation error has
ONE explicit budget chosen before the smoothing index. Windows may
vary with frequency, and the cap includes all initial triangles. -/
theorem energy (hcoeff:P.coefficient=(fun z=>κ+aV z))
    (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (n:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D htau htau1 hcontract n)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient n)
    {B K:ℝ}(hB:∀x,|a x|≤B)(hK:0≤K)
    (hholder:∀x y,|a x-a y|≤K*|x-y|^D.beta)
    (hlocal:StandardTerminalPastLocality J)(w:ℕ→ℝ≥0)(s:Finset ℕ)(depth:ℕ)
    (hpos:∀j∈s,0<w j)(hwH:∀j∈s,w j≤H)(hw1:∀j∈s,(w j:ℝ)≤1)
    (hspan:∀j∈s,(w j:ℝ)≤P.horizon)
    (hold:∀j∈s,∀i,i<depth→(w j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k))
    (hL:1≤Λ)(ρ:ℝ)(hρ:0≤ρ):
    Integrable (fun z:ℝ≥0×Ω=>‖∑j∈s,Val (w j) j depth hL ρ hρ z‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖∑j∈s,Val (w j) j depth hL ρ hρ z‖^2 ∂energyMeasure μ H)≤
        (ScalarApproximationDiscrepancy.scalarError D n)^2*
          budget (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract)
            κ M H Λ ρ B K D.beta depth B0 s:=by
  let Q:=ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract
  let F:ℕ→ℝ≥0×Ω→CircleL2:=fun j=>Val (w j) j depth hL ρ hρ
  have hFm(j:ℕ):Measurable (F j):=FullOrdinaryHeatBandError.measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP (w j) j depth hL ρ hρ
  have he(j:ℕ)(hj:j∈s):Integrable (fun z:ℝ≥0×Ω=>‖F j z‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖F j z‖^2 ∂energyMeasure μ H)≤
        (ScalarApproximationDiscrepancy.scalarError D n)^2*bandBudget Q κ M H Λ ρ B K D.beta depth B0 j:=by
    have he:=FullOrdinaryHeatBandError.energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha haP J hIJ₀ hIJ₁ hnull hJ hsmall
      hcoeff D htau htau1 hcontract n hP hU hV hB hK hholder hlocal (w j)
      (hpos j hj) (hwH j hj) (hw1 j hj) (hspan j hj) j depth (hold j hj) B0 hBDG hL ρ hρ
    exact ⟨he.1,he.2.trans_eq (by unfold bandBudget;ring)⟩
  exact HilbertFiniteEnergy.approximation (energyMeasure μ H) s F hFm
    (fun j hj=>(he j hj).1) (ScalarApproximationDiscrepancy.scalarError D n)
    (bandBudget Q κ M H Λ ρ B K D.beta depth B0) (fun j hj=>(he j hj).2)
end SHE.FullOrdinaryFiniteBandError
