module
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

namespace SHE.FullOrdinaryHeatBandError
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
variable (haP:SmoothCylinders.BoundedSmooth P.coefficient)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

def value (w:ℝ≥0)(j depth:ℕ)(hL:1≤Λ)(ρ:ℝ)(hρ:0≤ρ):ℝ≥0×Ω→CircleL2:=
  FullOrdinaryErrorOutput.field
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP w
      (RootFamily j) (RootUniform j) (RootMeasurable j) hL hρ depth
local notation "Val"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP

theorem measurable (w:ℝ≥0)(j depth:ℕ)(hL:1≤Λ)(ρ:ℝ)(hρ:0≤ρ):
    Measurable (Val w j depth hL ρ hρ):=
  FullOrdinaryErrorOutput.measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP w
      (RootFamily j) (RootUniform j) (RootMeasurable j) hL hρ depth

include hsmall hIJ₀ hIJ₁ hnull hJ hAs in
/-- The literal actual ordinary-error sum, at a constructed first-pair
heat band and on the full output clock, has one numerical budget before
the companion smoothing index. All root jets and Holder moduli are
internally discharged. -/
theorem energy (hcoeff:P.coefficient=(fun z=>κ+aV z))
    (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (n:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D htau htau1 hcontract n)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient n)
    {B K:ℝ}(hB:∀x,|a x|≤B)(hK:0≤K)
    (hholder:∀x y,|a x-a y|≤K*|x-y|^D.beta)
    (hlocal:StandardTerminalPastLocality J)(w:ℝ≥0)(hpos:0<w)(hwH:w≤H)(hw1:(w:ℝ)≤1)
    (hspan:(w:ℝ)≤P.horizon)(j depth:ℕ)
    (hold:∀i,i<depth→(w:ℝ)≤PhysicalScoreChain.uniformHorizon 1 i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k))
    (hL:1≤Λ)(ρ:ℝ)(hρ:0≤ρ):
    Integrable (fun z:ℝ≥0×Ω=>‖Val w j depth hL ρ hρ z‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖Val w j depth hL ρ hρ z‖^2 ∂energyMeasure μ H)≤
        (H:ℝ)*(Λ^(-ρ)*(ScalarApproximationDiscrepancy.scalarError D n)^2*
          MixedPastNewestFiniteError.constant
            (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract) κ M 0 1
              (2*B) (2*K) depth B0
                (ScalarHeatBandBernstein.amplitude B K D.beta depth*((2:ℝ)^(j+1))^(-D.beta))
                  ((2:ℝ)^(j+1))):=by
  let A:=ScalarHeatBandBernstein.amplitude B K D.beta depth
  let ν:ℝ:=(2:ℝ)^(j+1)
  have hA:0≤A:=ScalarHeatBandBernstein.amplitude_nonneg hK depth
  have hν:0≤ν:=by dsimp only [ν];positivity
  have hB0:0≤B:=(abs_nonneg (a 0)).trans (hB 0)
  have hexp:P.exponent=D.beta:=by rw [hP];rfl
  have hroot:∀x z,|(RootFamily j) x z|≤2*B:=by
    intro x z
    exact ScalarHeatBandHolder.band_bound ha hB j (z 0)
  have hrootmod:∀x z y,|(RootFamily j) x z-(RootFamily j) x y|≤(2*K)*|z 0-y 0|^P.exponent:=by
    intro x z y
    rw [hexp]
    exact ScalarHeatBandHolder.band_holder ha hB hholder j (z 0) (y 0)
  have hjets:∀x l,l≤depth→∀z,‖iteratedFDeriv ℝ l ((RootFamily j) x) z‖≤(A*ν^(-D.beta))*ν^l:=by
    intro x l hl z
    have hj:=ScalarHeatRootBands.test_jets ha hB hK D.beta_pos.le D.beta_le_one hholder
      (fun _:HeatCircle=>(1:ℝ)) (W:=1) zero_le_one (fun _=>by norm_num) depth (j+1) x l hl z
    have he:ScalarHeatRootBands.test a (fun _:HeatCircle=>(1:ℝ)) (j+1) x=Root j:=by
      funext y
      exact one_mul _
    rw [he] at hj
    simpa only [one_mul] using hj
  exact FullOrdinaryErrorOutput.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP w
      (RootFamily j) (RootUniform j) (RootMeasurable j) hL hρ
      J hIJ₀ hIJ₁ hnull hJ hAs hsmall hcoeff D htau htau1 hcontract n hP hU hV
      (mul_nonneg (by norm_num) hB0) (mul_nonneg (by norm_num) hK) hroot hrootmod
      hlocal hpos hwH hw1 hspan depth hold (A*ν^(-D.beta)) ν
        (mul_nonneg hA (rpow_nonneg hν _)) hν hjets B0 hBDG
end SHE.FullOrdinaryHeatBandError
