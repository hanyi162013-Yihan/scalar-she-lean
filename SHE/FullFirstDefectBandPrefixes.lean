module
public import SHE.FullFirstDefectBandSections
public import SHE.FullFirstDefectBandEnergy
public import SHE.HilbertBandTails
public import SHE.HilbertDyadicConvergence
public import SHE.CanonicalDefectCosts
public import SHE.RemainderBandSpans
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

namespace SHE.FullFirstDefectBandPrefixes
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
open Filter
open scoped Topology
local instance fullFirstDefectBandSeries_second:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local notation "Term"=>FullFirstDefectBandEnergy.term
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

set_option backward.isDefEq.respectTransparency true in
include hsmall in
theorem prefixes (hM:0≤M)(hP:P.coefficient=(fun z=>κ+aV z))
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(N J0:ℕ)
    {B K β:ℝ}(hB:∀z,|a z|≤B)(hK:0≤K)(hβ:0<β)(hβ1:β≤1)
    (hHolder:∀x y,|a x-a y|≤K*|x-y|^β)
    (η:ℝ)(hη:0<η)(hηβ:η<β)
    (hOne:(RemainderBandSpans.span β (J0+1):ℝ)≤1)
    (hProfile:(RemainderBandSpans.span β (J0+1):ℝ)≤P.horizon)
    (hAge:∀k,k≤N→(RemainderBandSpans.span β (J0+1):ℝ)≤
      ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k)
    (hOld:∀r,r<N→(RemainderBandSpans.span β (J0+1):ℝ)≤uniformHorizon 1 r)
    (G:ℕ→ℝ≥0×Ω→CircleL2)(hG:∀n,Measurable (G n))
    (hEq:∀n,∀ᵐt:ℝ≥0∂timeMeasure H,∀ᵐω:Ω∂μ,
      G n (t,ω)=∑k∈Finset.range (N+1),Term (RemainderBandSpans.span β (J0+n+1)) (J0+n) hL hρ.le k (t,ω)):
    let C:=DefectGapFiniteCoefficient.constant P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
      (ScalarHeatBandBernstein.amplitude B K β N) η N
        (fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i P)
    ∃hi:∀n,Integrable (fun z=>‖G n z‖^2) (energyMeasure μ H),
      let V:=HilbertBandTails.vector (energyMeasure μ H) G hG hi
      (∑'n,‖V n‖)≤sqrt C*DefectGapFiniteCoefficient.clock Λ ρ*StateBands.geometricConstant (β-η)*
        ((2:ℝ)^(J0+1))^(-(β-η))*sqrt (Neg ρ).toReal ∧
      ∀L:ℕ,Integrable (fun z=>‖∑n∈Finset.range L,G n z‖^2) (energyMeasure μ H) ∧
        sqrt (∫z,‖∑n∈Finset.range L,G n z‖^2 ∂energyMeasure μ H)≤
          sqrt C*DefectGapFiniteCoefficient.clock Λ ρ*StateBands.geometricConstant (β-η)*
            ((2:ℝ)^(J0+1))^(-(β-η))*sqrt (Neg ρ).toReal:=by
  intro C
  let γ:=β-η
  let R:ℝ:=(2:ℝ)^(J0+1)
  let D:=sqrt C*DefectGapFiniteCoefficient.clock Λ ρ*sqrt (Neg ρ).toReal
  have hγ:0<γ:=sub_pos.mpr hηβ
  have hR:0<R:=by dsimp only [R];positivity
  have hC:0≤C:=DefectGapFiniteCoefficient.constant_nonneg _ _ _ _ _ _ _
  have hclock:0≤DefectGapFiniteCoefficient.clock Λ ρ:=
    DefectGapFiniteCoefficient.clock_nonneg (zero_le_one.trans hL) hρ
  have hD:0≤D:=by dsimp only [D];positivity
  have hspan(n:ℕ):(RemainderBandSpans.span β (J0+n+1):ℝ)≤RemainderBandSpans.span β (J0+1):=by
    exact_mod_cast RemainderBandSpans.span_antitone hβ.le (show J0+1≤J0+n+1 by omega)
  have he(n:ℕ):Integrable (fun z=>‖G n z‖^2) (energyMeasure μ H) ∧
      (∫z,‖G n z‖^2 ∂energyMeasure μ H)≤
        C*DefectGapFiniteCoefficient.clock Λ ρ^2*((2:ℝ)^(J0+n+1))^(-2*γ)*(Neg ρ).toReal:=
    FullFirstDefectBandSections.energy_sections
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha hsmall
        hM hP ρ hL hρ hρhalf N (RemainderBandSpans.span β (J0+n+1))
          (RemainderBandSpans.span_pos β _) ((hspan n).trans hOne) ((hspan n).trans hProfile)
            (fun k hk=>(hspan n).trans (hAge k hk)) (fun r hr=>(hspan n).trans (hOld r hr))
              hB hK hβ.le hβ1 hHolder (J0+n) η hη (G n) (hG n) (hEq n)
  let hi:=fun n=>(he n).1
  let V:=HilbertBandTails.vector (energyMeasure μ H) G hG hi
  have hv(n:ℕ):‖V n‖≤D*(R*(2:ℝ)^n)^(-γ):=by
    let ν:ℝ:=(2:ℝ)^(J0+n+1)
    have hν:0<ν:=by dsimp only [ν];positivity
    have hνeq:ν=R*(2:ℝ)^n:=by dsimp only [ν,R];rw [show J0+n+1=J0+1+n by omega,pow_add]
    have hp:ν^(-2*γ)=(ν^(-γ))^2:=by
      rw [←rpow_mul_natCast hν.le]
      congr 1
      ring
    have hh:= (he n).2
    rw [←HilbertBandTails.vector_norm_sq (energyMeasure μ H) G hG hi n] at hh
    change ‖V n‖^2≤C*DefectGapFiniteCoefficient.clock Λ ρ^2*ν^(-2*γ)*(Neg ρ).toReal at hh
    rw [hp] at hh
    have hsq:‖V n‖^2≤(D*ν^(-γ))^2:=hh.trans_eq (by
      dsimp only [D]
      rw [mul_pow,mul_pow,mul_pow,sq_sqrt hC,sq_sqrt ENNReal.toReal_nonneg]
      ring)
    have hn:0≤D*ν^(-γ):=mul_nonneg hD (rpow_nonneg hν.le _)
    rw [←hνeq]
    exact (sq_le_sq₀ (norm_nonneg _) hn).mp hsq
  have hs:=StateBands.vector_geometric_bands hγ hR hD V hv
  have hmajor:Summable (fun n=>D*(R*(2:ℝ)^n)^(-γ)):=
    (StateBands.geometric_bands hγ hR).1.mul_left D
  have hnorm:Summable (fun n=>‖V n‖):=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hv hmajor
  have htotal:(∑'n,‖V n‖)≤sqrt C*DefectGapFiniteCoefficient.clock Λ ρ*
      StateBands.geometricConstant (β-η)*((2:ℝ)^(J0+1))^(-(β-η))*sqrt (Neg ρ).toReal:=by
    calc
      _≤∑'n,D*(R*(2:ℝ)^n)^(-γ):=hnorm.tsum_le_tsum hv hmajor
      _=D*StateBands.geometricConstant γ*R^(-γ):=by
        rw [tsum_mul_left,(StateBands.geometric_bands hγ hR).2]
        ring
      _=_:=by dsimp only [D,R,γ];ring
  have hrep:∀ᵐz∂energyMeasure μ H,∀n,V n z=G n z:=by
    rw [ae_all_iff]
    intro n
    exact ((memLp_two_iff_integrable_sq_norm (hG n).aestronglyMeasurable).mpr (hi n)).coeFn_toLp
  refine ⟨hi,htotal,fun L=>?_⟩
  let W:Lp CircleL2 2 (energyMeasure μ H):=∑n∈Finset.range L,V n
  have he:(fun z=>W z)=ᵐ[energyMeasure μ H] (fun z=>∑n∈Finset.range L,G n z):=by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range L) V,hrep] with z hz hr
    exact hz.trans (Finset.sum_congr rfl (fun n _=>hr n))
  have hiW:Integrable (fun z=>‖W z‖^2) (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable W)).mp (Lp.memLp W)
  have hEq:(∫z,‖∑n∈Finset.range L,G n z‖^2 ∂energyMeasure μ H)=‖W‖^2:=by
    rw [PredictableL2.realLp_norm_sq]
    exact integral_congr_ae (he.symm.mono (fun _ hz=>congrArg (fun e:CircleL2=>‖e‖^2) hz))
  refine ⟨hiW.congr (he.mono (fun _ hz=>congrArg (fun e:CircleL2=>‖e‖^2) hz)),?_⟩
  rw [hEq,Real.sqrt_sq (norm_nonneg _)]
  exact (norm_sum_le (Finset.range L) V).trans
    ((hnorm.sum_le_tsum (Finset.range L) (fun n hn=>norm_nonneg _)).trans htotal)
end SHE.FullFirstDefectBandPrefixes
