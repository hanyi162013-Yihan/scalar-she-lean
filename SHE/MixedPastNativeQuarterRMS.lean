module
public import SHE.MixedPastNativeEnergyNormalization
public import SHE.NativeHigherRMSAlgebra
public import SHE.NativeHigherQuarterTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedPastNativeQuarterRMS
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeQuarterRMS_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeQuarterRMS_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeQuarterRMS_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeQuarterRMS_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeQuarterRMS_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeQuarterRMS_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastNativeQuarterRMS_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeQuarterRMS_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeQuarterRMS_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total

def prefactor (k:ℕ)(ρ:ℝ):ℝ:=
  (κ+M)*((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ

def coefficient (k:ℕ)(Cf ρ:ℝ):ℝ:=
  prefactor κ (M:=M) k ρ*(4*Cf/(3*(P.lower/8)))*NativeHeatSpan.sqrtKernelConstant^2*
    (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2

theorem prefactor_nonneg (k:ℕ){ρ:ℝ}(hρhalf:ρ<1/2)(hκ0:0≤κ)(hM:0≤M):
    0≤prefactor κ (M:=M) k ρ:=by
  have hG:0≤GaussianNegativePacket.constant ρ:=by
    unfold GaussianNegativePacket.constant
    linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf,GaussianNegativePacket.traceConstant_pos]
  unfold prefactor
  positivity

theorem coefficient_nonneg (k:ℕ){Cf ρ:ℝ}(hCf:0≤Cf)(hρhalf:ρ<1/2)(hκ0:0≤κ)(hM:0≤M):
    0≤coefficient κ (M:=M) P k Cf ρ:=by
  have hp:=prefactor_nonneg κ k hρhalf hκ0 hM
  have hlower:=P.lower_pos
  unfold coefficient
  positivity

/-- The actual native quarter trace is controlled by the precise two
RMS densities whose original old-time integrals are already checked. -/
theorem cap (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(A0 ν ρ Cf Cdim χ:ℝ)(p:ℕ)(Bcur Bword:ℝ≥0)
    (hCf:0≤Cf)(hCdim:0≤Cdim)(hρ:0≤ρ)(hρhalf:ρ<1/2)(hA0:0≤A0)(hν:0≤ν)
    (hq:v<q)(hqb:(q:ℝ)<(b:ℝ))(hq1:(q:ℝ)≤1)
    (ha:QuarterSpatialEvent.active Zero (b:ℝ) k q t):
    let a:=QuarterSpatialEvent.anchor k t
    let δ:=(carrier Zero k).terminal a-(q:ℝ)
    let r:=(q:ℝ)+δ/4
    let sharp:=MixedPastWordMoments.total (d:=1) P
      (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ))
      (fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
    let K:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
      (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
    let c:=Real.sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal a-r)))*NativeHeatSpan.sqrtKernelConstant
    let C:=coefficient κ (M:=M) P k Cf ρ
    let Ccur:=Real.sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) P k p χ Cdim Bcur)
    let Cpast:=Real.sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) P k Bword)
    (κ+M)*(((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
      (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
        (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword)))≤
      (((b:ℝ)-(q:ℝ))^(ρ/2)*(Ccur*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ)^(χ/2)*
        PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower) (uniformConstant 1)
          k q ((2-χ)/4) A0 ν a+
        Cpast*sqrt (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ))*
        PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower) (uniformConstant 1)
          k q (1/2:ℝ) A0 ν a))^2 :=by
  intro a δ r sharp K c C Ccur Cpast
  have hterm:(carrier Zero k).terminal a=ActualMeanKernel.fixedTerminal
      (R:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t:=
    ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl) k t _ _
  have hδ:0<δ:=by dsimp only [δ];rw [hterm];exact sub_pos.mpr ha.2
  have hW:0≤timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a:=
    timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k a ha.1
  have hsharp:0≤sharp:=by
    change 0≤PastWordTimeFields.total Zero P k a A0 ν
    exact PastWordTimeFields.total_nonneg Zero P k a A0 ν
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hP:=P.lower_pos
  have hC:=coefficient_nonneg κ P k hCf hρhalf hκ.le hM
  have hCc:=MixedPastNativeEnergyNormalization.currentCoefficient_nonneg κ P k p χ Cdim Bcur hCdim hκ.le hM
  have hCp:=MixedPastNativeEnergyNormalization.pastCoefficient_nonneg κ (M:=M) P k Bword
  have hCur:=MixedPastNativeEnergyNormalization.current_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k q t p χ Cdim Bcur hCdim hδ
  have hPast:=MixedPastNativeEnergyNormalization.past_le
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k q t A0 ν Bword (sub_pos.mpr (NNReal.coe_lt_coe.mpr hq)) (by have hv0:=v.2;linarith)
  have hδr:(carrier Zero k).terminal a-r=3*δ/4:=by dsimp only [r,δ];ring
  have hbr:0<(b:ℝ)-r:=by
    have htb:(carrier Zero k).terminal a≤(b:ℝ):=(terminal_le_initial Zero k a).trans_eq (by rfl)
    dsimp only [r,δ]
    linarith
  have hclock:NativeHeatSpan.clock ((b:ℝ)-r)≤(b:ℝ)-(q:ℝ):=by
    unfold NativeHeatSpan.clock
    apply (div_le_iff₀ (by positivity : 0<4*Real.pi^2)).mpr
    have hπ:=Real.pi_gt_three
    have hw:=sub_pos.mpr hqb
    have hπ1:1≤4*Real.pi^2:=by nlinarith [sq_nonneg (Real.pi-3)]
    dsimp only [r]
    nlinarith
  have hCur0:0≤CurrentEnergy k q t p χ Cdim Bcur:=by rw [hCur];positivity
  have hPast0:0≤PastEnergy k q t A0 ν Bword:=by unfold MixedPastNativeKernelActual.pastEnergy;positivity
  have hb:=NativeHigherQuarterTrace.bound (prefactor κ (M:=M) k ρ) Cf (P.lower/8)
    NativeHeatSpan.sqrtKernelConstant (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
    (timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a)
    (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword)
    (NativeHeatSpan.clock ((b:ℝ)-r)) ((b:ℝ)-(q:ℝ)) δ ρ
    (prefactor_nonneg κ k hρhalf hκ.le hM) hCf (by positivity) (by positivity)
    (NativeHeatSpan.clock_pos hbr).le hclock hδ hρ
  have hfirst:
      (κ+M)*(((1+k:ℕ):ℝ)^2*(4*Real.pi^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
        (NativeHeatSpan.clock ((b:ℝ)-r))^ρ*((c*K)^2*
          (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword)))≤
        C*((b:ℝ)-(q:ℝ))^ρ*δ⁻¹*(timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a)^2*
          (8*sharp^2*CurrentEnergy k q t p χ Cdim Bcur+2*PastEnergy k q t A0 ν Bword):=by
    convert! hb using 1 <;> dsimp only [C,coefficient,prefactor,c,K] <;> simp only [hδr] <;> ring
  have hEq:0≤∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  have hEv:0≤∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  have hsplit:=NativeHigherRMSAlgebra.trace_split C
    (MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) P k p χ Cdim Bcur)
    (MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) P k Bword)
    ((b:ℝ)-(q:ℝ)) δ ((q:ℝ)-(v:ℝ))
    (∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ) (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
    (timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a) sharp ρ χ
    (CurrentEnergy k q t p χ Cdim Bcur) (PastEnergy k q t A0 ν Bword)
    hC hCc hCp (sub_pos.mpr hqb) hδ (sub_pos.mpr (NNReal.coe_lt_coe.mpr hq)) hEq hEv hW hsharp hCur hPast
  have hactive:StrictHistory Zero k a ∧ (q:ℝ)<(carrier Zero k).terminal a:=⟨ha.1,sub_pos.mp hδ⟩
  have hIcur:PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower) (uniformConstant 1)
      k q ((2-χ)/4) A0 ν a=δ^((2-χ)/4-1)*(timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*sharp):=by
    simp only [PastMeanTimeFactors.totalIntegrand,if_pos hactive]
    rfl
  have hIpast:PastMeanTimeFactors.totalIntegrand Zero P (fraction P*P.lower) (uniformConstant 1)
      k q (1/2:ℝ) A0 ν a=δ^(-(1/2:ℝ))*(timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*sharp):=by
    simp only [PastMeanTimeFactors.totalIntegrand,if_pos hactive,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num]
    rfl
  rw [hIcur,hIpast]
  convert! hfirst.trans hsplit using 1 <;> dsimp only [Ccur,Cpast] <;> ring

end SHE.MixedPastNativeQuarterRMS

