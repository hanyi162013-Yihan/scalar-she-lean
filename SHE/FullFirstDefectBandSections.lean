module
public import SHE.FullFirstDefectBandEnergy
public import SHE.MixedFirstDefectRelativeFields
public import SHE.MixedFirstDefectHeatBandBound
public import SHE.MixedFirstDefectFiniteBandEnergy
public import SHE.DefectGapFiniteCoefficient
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

namespace SHE.FullFirstDefectBandSections
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
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a)
local notation "Root" j:max=>(fun z:WordRecursion.State 1=>ScalarHeatBands.band a (j+1) (z 0))
local notation "RootSmooth" j:max=>(ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right (EuclideanSpace.proj (0:Fin 1))
local notation "RootFamily" j:max=>(fun _:HeatCircle=>Root j)
local notation "RootUniform" j:max=>UniformSmooth.UniformBoundedSmooth.fixed (P:=HeatCircle) (RootSmooth j)
local notation "RootMeasurable" j:max=>(RootSmooth j).smooth.continuous.measurable.comp
  (measurable_snd:Measurable (Prod.snd:HeatCircle×WordRecursion.State 1→WordRecursion.State 1))

local notation "Term"=>FullFirstDefectBandEnergy.term
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- The actual finite sum of first-defect marks has the full output-time
energy bound. Only the equality of one Borel output version to the literal
finite sum is supplied; every analytic norm/space/time premise is proved. -/
theorem energy_sections (hM:0≤M)(hP:P.coefficient=(fun z=>κ+aV z))
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(N:ℕ)
    (h:ℝ≥0)(hh:0<h)(hh1:(h:ℝ)≤1)(hspanP:(h:ℝ)≤P.horizon)
    (hAge:∀k,k≤N→(h:ℝ)≤ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k)
    (hOld:∀r,r<N→(h:ℝ)≤uniformHorizon 1 r)
    {B K β:ℝ}(hB:∀z,|a z|≤B)(hK:0≤K)(hβ:0≤β)(hβ1:β≤1)
    (hHolder:∀x y,|a x-a y|≤K*|x-y|^β)(j:ℕ)
    (η:ℝ)(hη:0<η)(G:ℝ≥0×Ω→CircleL2)(hG:Measurable G)
    (hEq:∀ᵐt:ℝ≥0∂timeMeasure H,∀ᵐω:Ω∂μ,
      G (t,ω)=∑k∈Finset.range (N+1),Term h j hL hρ.le k (t,ω)):
    Integrable (fun z:ℝ≥0×Ω=>‖G z‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖G z‖^2 ∂energyMeasure μ H)≤
        DefectGapFiniteCoefficient.constant P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          (ScalarHeatBandBernstein.amplitude B K β N) η N
            (fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i P)*
          DefectGapFiniteCoefficient.clock Λ ρ^2*((2:ℝ)^(j+1))^(-2*(β-η))*(Neg ρ).toReal:=by
  let A:=ScalarHeatBandBernstein.amplitude B K β N
  let ν:ℝ:=(2:ℝ)^(j+1)
  let Cs:Fin (N+1)→ℝ:=fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i P
  have hA:0≤A:=ScalarHeatBandBernstein.amplitude_nonneg hK N
  have hν:1≤ν:=one_le_pow₀ (by norm_num:(1:ℝ)≤2)
  have hhR:0<(h:ℝ):=by exact_mod_cast hh
  have hspan(b:ℝ≥0):(b:ℝ)-((b-h:ℝ≥0):ℝ)≤(h:ℝ):=by
    by_cases hb:h≤b
    · rw [NNReal.coe_sub hb]
      linarith only
    · rw [tsub_eq_zero_of_le (le_of_not_ge hb),NNReal.coe_zero,sub_zero]
      exact_mod_cast le_of_not_ge hb
  have hpos(b:ℝ≥0)(hb:0<b):b-h<b:=by
    by_cases hh':h≤b
    · apply NNReal.coe_lt_coe.mp
      rw [NNReal.coe_sub hh']
      have hbR:0<(b:ℝ):=by exact_mod_cast hb
      linarith only [hhR,hbR]
    · rw [tsub_eq_zero_of_le (le_of_not_ge hh')]
      exact hb
  have hδ0:0<ControlledOldIntervals.fraction P*P.lower:=
    mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  have hρone:ρ≤1:=hρhalf.le.trans (by norm_num)
  have hmap:Measurable (fun z:ℝ≥0×Ω=>((z.1:ℝ),z.2)):=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hrel(i:Fin (N+1)):Measurable (fun z:ℝ≥0×Ω=>MixedFirstDefectRelativeEnergy.value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
        (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h (A*ν^(-β)) ν i ρ hL hρ.le ((z.1:ℝ),z.2)):=by
    have hm:=MixedFirstDefectRelativeFields.measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
        (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h (A*ν^(-β)) ν i
          hδ0 hhR (fun r=>(uniformConstant_pos 1 r).le)
            (mul_nonneg hA (rpow_nonneg (zero_le_one.trans hν) _)) (zero_le_one.trans hν) ρ hL hρ hρone
    exact hm.comp hmap
  have hmajor:Measurable (fun z:ℝ≥0×Ω=>∑i:Fin (N+1),Cs i*MixedFirstDefectRelativeEnergy.value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
        (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h (A*ν^(-β)) ν i ρ hL hρ.le ((z.1:ℝ),z.2)):=
    Finset.measurable_sum _ (fun i _=>(hrel i).const_mul (Cs i))
  have hb:∀ᵐz:ℝ≥0×Ω∂energyMeasure μ H,
      ‖G z‖≤∑i:Fin (N+1),Cs i*MixedFirstDefectRelativeEnergy.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
          (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h (A*ν^(-β)) ν i ρ hL hρ.le ((z.1:ℝ),z.2):=by
    have hsections:∀ᵐt:ℝ≥0∂timeMeasure H,∀ᵐω:Ω∂μ,
      ‖G (t,ω)‖≤∑i:Fin (N+1),Cs i*MixedFirstDefectRelativeEnergy.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
          (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h (A*ν^(-β)) ν i ρ hL hρ.le ((t:ℝ),ω):=by
      filter_upwards [hEq,timeMeasure_ae_mem H] with t htEq ht
      filter_upwards [htEq] with ω hz
      let z:ℝ≥0×Ω:=(t,ω)
      rw [hz,←Fin.sum_univ_eq_sum_range]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have hk:(i:ℕ)≤N:=Nat.le_of_lt_succ i.isLt
      have hs:=hspan z.1
      have hc:=MixedFirstDefectHeatBandBound.norm_le
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs (z.1-h) z.1 (tsub_le_self) ha hsmall
          hM hP ρ hL hρ hρhalf N i hk (hs.trans hspanP) (hs.trans (hAge i hk))
            (fun r hr=>hs.trans (hOld r (Nat.lt_of_lt_of_le hr hk))) h hhR hs (hpos z.1 ht.1) ht.2
              hB hK hβ hβ1 hHolder j z.2
      exact hc
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_le hG.norm hmajor)).mpr hsections
  have hδ:0<ControlledOldIntervals.fraction P*P.lower:=
    mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  have hρ1:ρ≤1:=hρhalf.le.trans (by norm_num)
  have he:=MixedFirstDefectFiniteBandEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
      (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h A β η ν N
        hδ hhR hh1 (fun r=>(uniformConstant_pos 1 r).le) hA hη hν ρ hL hρ hρ1 Cs G hG hb
  refine ⟨he.1,?_⟩
  rw [DefectGapFiniteCoefficient.coefficient_eq] at he
  exact he.2

end SHE.FullFirstDefectBandSections
