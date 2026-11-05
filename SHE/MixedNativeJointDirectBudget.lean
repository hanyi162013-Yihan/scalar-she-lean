module

public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeMovingJointBudgets
public import SHE.MixedNativeJointPositiveCurrent
public import SHE.NativeJointCurrentBudget
public import SHE.MixedNativePastBudget
public import SHE.GammaBandConstants
public import SHE.NativeMovingGammaClock
public import SHE.MixedMovingEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.MixedNativeJointDirectBudget
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedNativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedNativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeMovingCurrentGamma_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeMovingCurrentGamma_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeMovingCurrentGamma_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_blockSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeMovingCurrentGamma_blockBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance mixedNativeMovingCurrentGamma_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedNativeMovingCurrentGamma_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeMovingCurrentGamma_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower)
variable (h W:ℝ) (hh:0<h) (hhP:h≤P.horizon) (hW0:0≤W) (hcover:W+h≤H)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)

local notation "Past"=>NativeMovingGammaClock.past W
local notation "Terminal"=>NativeMovingGammaClock.terminal W h
local notation "covered" r=>NativeMovingGammaClock.terminal_le hW0 hh.le H hcover r
local notation "ordered" r=>NativeMovingGammaClock.past_lt hW0 hh r
local notation "span" r=>NativeMovingGammaClock.span hW0 hh.le r
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "Budget"=>MixedNativeMovingJointBudgets.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hH P hκP h W hh hW0 hcover

def direct (a:ℝ→ℝ)(j:ℕ)(ρ:ℝ)(r:ℝ):ℝ≥0∞:=NativeJointCurrentBudget.value μ P
  (Function.uncurry S.first) (Function.uncurry S.second) Λ H a j ρ h r
local notation "Direct"=>direct 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P h

theorem direct_measurable {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a)(j:ℕ)(ρ:ℝ):Measurable (Direct a j ρ):=
  NativeJointCurrentBudget.measurable 𝓕 μ P (Function.uncurry S.first) (Function.uncurry S.second)
    S.first_predictable S.second_predictable Λ H ha j ρ h

include hh hW0 hcover in
/-- The genuine Borel current budget is precisely the native row slot
on every covered original moving-past window. -/
theorem current_eq {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){A:ℝ}(hA:0≤A)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent)(j:ℕ)(ρ r:ℝ)(hr:r∈Ioc (0:ℝ) W):
    Budget a j ρ 0 1 r=Direct a j ρ r:=by
  change Budget a j ρ 0 1 r=NativeJointCurrentBudget.value μ P
    (Function.uncurry S.first) (Function.uncurry S.second) Λ H a j ρ h r
  rw [NativeJointCurrentBudget.native_eq 𝓕 μ P H (Function.uncurry S.first) (Function.uncurry S.second)
    S.first_predictable S.second_predictable Λ ha hA hholder j ρ hr.1 (by linarith [hr.2,hcover])]
  dsimp only [MixedNativeMovingJointBudgets.budget,MixedNativeJointRowBudgets.timeBudget]
  rw [span r]
  change (∫⁻τ in Ioc (0:ℝ) h,∫⁻ω,ENNReal.ofReal (τ^(ρ-1/2)*
    ‖NativeRandomRows.nativeRow (NativeJointRowClock.field P (Function.uncurry S.first) (Function.uncurry S.second)
      Λ (Past r) (Terminal r) a j 0) (((Terminal r:ℝ)-τ).toNNReal,ω)-
      NativeRandomRows.nativeRow (NativeJointRowClock.field P (Function.uncurry S.first) (Function.uncurry S.second)
        Λ (Past r) (Terminal r) a j 1) (((Terminal r:ℝ)-τ).toNNReal,ω)‖^2) ∂μ)=_
  rw [NativeMovingGammaClock.past_eq hr,NativeMovingGammaClock.terminal_eq hr h]
  rw [Real.coe_toNNReal _ (by linarith [hr.1]:0≤r+h)]

include hIJ₀ hIJ₁ hΛ hH hBDG hh hW0 hcover in
/-- Full actual SAME-J direct current budget, ready for a measurable
outer sum with the other five pointwise slot envelopes. -/
theorem energy {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A ρ:ℝ}
    (hA:0≤A) (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2)
    (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ):
    (∫⁻r in Ioc (0:ℝ) W,Direct a j ρ r)≤ENNReal.ofReal
      (GammaBandConstants.gradient P A ρ*CompactMollifier.radius (j+1)^(2*P.exponent+4*ρ)*
        min 1 ((4*Global)/CompactMollifier.radius (j+1)^2)):=by
  have hh1:h≤1:=by linarith
  have hW1:W≤1:=by linarith
  exact NativeJointCurrentBudget.energy 𝓕 μ P H (Function.uncurry S.first) (Function.uncurry S.second)
    S.first_predictable S.second_predictable
    (MixedMovingEnergy.global_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG)
    hΛ hh hh1 hW0 hW1 hcover hρ0 hρ1 ha hA hholder j
end SHE.MixedNativeJointDirectBudget
