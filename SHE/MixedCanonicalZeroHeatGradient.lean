module

public import SHE.MixedCanonicalGradientNoiseHeat
public import SHE.MixedCanonicalGradientHeat
public import SHE.NativeVariableTerminalCap
public import SHE.MixedCanonicalGradientAverage
public import SHE.TerminalItoRawLimit
public import SHE.WeightedHistoryL2Limit
public import SHE.RecursiveHeatGradientContinuity
public import SHE.NativeRowTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option quotPrecheck false
namespace SHE.MixedCanonicalZeroHeatGradient
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic GaussianItoTest ControlledProfile ControlledReferenceLevel
open Filter Topology
open scoped ENNReal NNReal
local instance mixedCanonicalZeroHeatGradient_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedCanonicalZeroHeatGradient_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedCanonicalZeroHeatGradient_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalZeroHeatGradient_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCanonicalZeroHeatGradient_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCanonicalZeroHeatGradient_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalZeroHeatGradient_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalZeroHeatGradient_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalZeroHeatGradient_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ) (hbH:b≤H)

variable (k:ℕ)
local notation "Obs" => (fun ε:ℝ≥0=>((L (0,0) ε k).observations.observations))
local notation "Terminal" => (fun ε:ℝ≥0=>((L (0,0) ε k).terminal))
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

local notation "Raw" => (fun ε:ℝ≥0=>MixedCanonicalGradientKernel.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k)
local notation "Noise" => (fun ε:ℝ≥0=>fun z:CutoffWordHistories.History Unit k×Ω=>
  MixedJointPastExpectedLevel.noiseVersion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter z.2) ε k) z.1 z.2)
local notation "R₀"=>ControlledReferenceLevel.referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)

include hIJ₀ hIJ₁ hnull hbH hsmall hΛ in
/-- Removing spatial regularization identifies the SAME original Ito
input with the literal zero-heat physical gradient kernel averaged over
the complete original history. Delta and smooth depth remain fixed. -/
theorem original_input (hJ:StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal:StandardTerminalPastLocality J)(hb1:(b:ℝ)≤1)
    {η:ℝ}(hη:0<η)(hgap:∀i,η≤(Z i).target-(b:ℝ))
    (ν:Measure Unit)[IsFiniteMeasure ν]:
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫h,Raw 0 (h,z) ∂CutoffWordHistories.historyMeasure R₀ ν k) ∧
      J.integral input=ᵐ[μ] fun ω=>∫h,Noise 0 (h,ω) ∂CutoffWordHistories.historyMeasure R₀ ν k:=by
  let σ:=CutoffWordHistories.historyMeasure R₀ ν k
  let out:=fun ε:ℝ≥0=>fun ω=>∫h,Noise ε (h,ω) ∂σ
  obtain ⟨B,hB,hBb⟩:=ControlledReferenceRecursiveResidualBounds.uniform_piece_bounds
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ k
  have hnm(ε:ℝ≥0):Measurable (Noise ε):=
    MixedCanonicalGradientAverage.noise_joint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k
  have hni(ε:ℝ≥0)(ω:Ω):Integrable (fun h=>Noise ε (h,ω)) σ:=
    Integrable.of_bound ((hnm ε).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun h=>(hBb (pastParameter ω) ε h ω).2.2.2.2))
  have hg:MemLp (out 0) 2 μ:=MemLp.of_bound
    ((hnm 0).stronglyMeasurable.integral_prod_left').aestronglyMeasurable (σ.real Set.univ*B)
      (Filter.Eventually.of_forall (fun ω=>by
        simpa only [out,mul_comm] using norm_integral_le_of_norm_le_const (μ:=σ)
          (Filter.Eventually.of_forall (fun h=>(hBb (pastParameter ω) 0 h ω).2.2.2.2))))
  let e:ℕ→ℝ≥0:=fun m=>(η/((m:ℝ)+1)).toNNReal
  have heq(m:ℕ):(e m:ℝ)=η/((m:ℝ)+1):=Real.coe_toNNReal _ (by positivity)
  have hep(m:ℕ):0<(e m:ℝ):=by rw [heq];positivity
  have heη(m:ℕ):(e m:ℝ)≤η:=by
    rw [heq]
    exact div_le_self hη.le (by linarith [Nat.cast_nonneg (α:=ℝ) m] : (1:ℝ)≤(m:ℝ)+1)
  have ht:Filter.Tendsto (fun m=>(e m:ℝ)) Filter.atTop (𝓝[>] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Filter.Eventually.of_forall hep⟩
    have hh:=tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ) |>.const_mul η
    simpa only [heq,mul_zero,div_eq_mul_inv,one_mul] using hh
  have htNN:Filter.Tendsto e Filter.atTop (𝓝 0):=by
    have hh:=continuous_real_toNNReal.continuousAt.tendsto.comp (ht.mono_right nhdsWithin_le_nhds)
    simpa only [Function.comp_def,Real.toNNReal_coe,Real.toNNReal_zero] using hh
  have hex(m:ℕ):∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫h,Raw (e m) (h,z) ∂σ) ∧
      J.integral input=ᵐ[μ] out (e m):=
    MixedCanonicalGradientAverage.original_average_input
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hΛ hbH
      (e m) (hep m) (fun i=>(heη m).trans (hgap i)) k hJ hlocal σ
  choose input hraw hrep using hex
  have hlim:Filter.Tendsto (fun m=>∫ω,‖out (e m) ω-out 0 ω‖^2 ∂μ) Filter.atTop (𝓝 0):=by
    have hh:=(MixedCanonicalGradientNoiseHeat.averaged_noise_limit
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ k ν).2.comp ht
    have hd(m:ℕ)(ω:Ω):out (e m) ω-out 0 ω=
        ∫h,Noise (e m) (h,ω)-Noise 0 (h,ω) ∂σ:=
      (integral_sub (hni (e m) ω) (hni 0 ω)).symm
    simpa only [Function.comp_def,Real.toNNReal_coe,hd,σ] using hh
  exact TerminalItoRawLimit.original_input 𝓕 μ H J input (fun m=>out (e m)) (out 0) hg hrep hlim
    (fun m z=>∫h,Raw (e m) (h,z) ∂σ) (fun z=>∫h,Raw 0 (h,z) ∂σ) hraw
    (MixedCanonicalGradientHeatAverage.average_tendsto
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ hbH k hb1 σ e htNN)

end SHE.MixedCanonicalZeroHeatGradient
