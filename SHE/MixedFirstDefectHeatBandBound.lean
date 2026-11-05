module
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

namespace SHE.MixedFirstDefectHeatBandBound
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

variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

/-- This is exactly the JT second term in the actual finite stochastic
comparison, with the original full first-defect normalization. -/
theorem value_eq_term (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(j k:ℕ)(ω:Ω):
    MixedFirstDefectRMS.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs
      1 v b hvb (RootFamily j) (RootUniform j) (RootMeasurable j) ρ hL hρ k ω=
        (JT j) hL hρ 2 k ω:=rfl

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- Actual heat-band first-defect bound, uniform in every band and
in the damping parameter at each fixed finite depth. Root jets are
proved from the constructed Gaussian heat bands. -/
theorem norm_le (hM:0≤M)(hP:P.coefficient=(fun z=>κ+aV z))
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(N k:ℕ)(hk:k≤N)
    (hspanP:(b:ℝ)-(v:ℝ)≤P.horizon)
    (hspanAge:(b:ℝ)-(v:ℝ)≤ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k)
    (hOld:∀r,r<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 r)
    (h:ℝ)(hh:0<h)(hspan:(b:ℝ)-(v:ℝ)≤h)(hpos:v<b)(hbH:b≤H)
    {B K β:ℝ}(hB:∀z,|a z|≤B)(hK:0≤K)(hβ:0≤β)(hβ1:β≤1)
    (hHolder:∀x y,|a x-a y|≤K*|x-y|^β)(j:ℕ)(ω:Ω):
    ‖(JT j) hL hρ.le 2 k ω‖≤
      ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf k P*
        MixedFirstDefectRelativeEnergy.value
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
            (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h
              (ScalarHeatBandBernstein.amplitude B K β N*((2:ℝ)^(j+1))^(-β))
                ((2:ℝ)^(j+1)) k ρ hL hρ.le (b,ω):=by
  let A:=ScalarHeatBandBernstein.amplitude B K β N
  let ν:ℝ:=(2:ℝ)^(j+1)
  have hA:0≤A:=ScalarHeatBandBernstein.amplitude_nonneg hK N
  have hν:0≤ν:=by dsimp only [ν];positivity
  have hjets:∀x l,l≤k→∀z,‖iteratedFDeriv ℝ l ((RootFamily j) x) z‖≤(A*ν^(-β))*ν^l:=by
    intro x l hl z
    have hj:=ScalarHeatRootBands.test_jets ha hB hK hβ hβ1 hHolder
      (fun _:HeatCircle=>(1:ℝ)) (W:=1) zero_le_one (fun _=>by norm_num) N (j+1) x l (hl.trans hk) z
    have he:ScalarHeatRootBands.test a (fun _:HeatCircle=>(1:ℝ)) (j+1) x=Root j:=by
      funext y
      change 1*ScalarHeatBands.band a (j+1) (y 0)=ScalarHeatBands.band a (j+1) (y 0)
      exact one_mul _
    rw [he] at hj
    simpa only [one_mul] using hj
  have hbnd:=MixedFirstDefectActualBound.norm_le
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs 1 v b hvb
      (RootFamily j) (RootUniform j) (RootMeasurable j) hsmall hM hP ρ hL hρ hρhalf k
        hspanP hspanAge hOld h hh hspan hpos hbH (A*ν^(-β)) ν
          (mul_nonneg hA (rpow_nonneg hν _)) hν hjets ω
  exact hbnd

end SHE.MixedFirstDefectHeatBandBound
