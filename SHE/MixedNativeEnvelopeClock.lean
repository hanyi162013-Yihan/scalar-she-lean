module
public import SHE.MovingNativeFourTermEnergy
public import SHE.NativeFourTermScale

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MixedNativeEnvelopeClock
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation Real
  ControlledProfile ControlledReferenceLevel ControlledOldIntervals NativeSignedHaarProcess PhysicalScoreChain
  SmoothCylinders UniformSmooth CutoffWordLevel
open scoped NNReal ENNReal
local instance mixedNativeEnvelopeClock_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeEnvelopeClock_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeEnvelopeClock_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeEnvelopeClock_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeEnvelopeClock_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeEnvelopeClock_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second


open Set
local notation "Env"=>MovingNativeFourTermEnergy.envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
local notation "Fcur"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Fneg"=>MixedNativeInputEnergyClock.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

/-- Exact active-clock decomposition of the literal complete native cap.
The factor nu^(-2 beta) is the actual squared band amplitude. -/
theorem completed (v h s:ℝ≥0)(hs:0<s)(hsh:s<h)(hvhH:v+h≤H)
    (k:ℕ)(A ν ρ χ ε tail η:ℝ)(hν:1≤ν)(hΛ:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(hχ:0≤χ)
    (p:ℕ)(Bcur Bword:ℝ≥0):
    let Cf:=NativeUniversalConstants.rowConstant (1+k)
    let Cdim:=NativeUniversalConstants.currentConstant.{0} (1+k) (by omega)
    let C:=MixedPastNativeQuarterRMS.coefficient κ (M:=M) P k Cf ρ
    let Ccur:=sqrt (8*C*MixedPastNativeEnergyNormalization.currentCoefficient κ (M:=M) P k p χ Cdim Bcur)
    let Cpast:=sqrt (2*C*MixedPastNativeEnergyNormalization.pastCoefficient κ (M:=M) P k Bword)
    let Jt:=MixedPastSignedEndpointMoments.traceConstant (Ω:=Ω) (M:=M) hell ρ hρ hρhalf
    let Cmom:=MixedPastWordMoments.momentConstant P k k p
      ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) Bcur κ M)^P.exponent)
    let Cgood:=PastSignedEndpointTime.goodCoefficient P k Jt ρ η
    let Cbad:=PastSignedEndpointTime.badCoefficient P k M Cmom
    let Gc:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k ρ χ ν ((h:ℝ)-(s:ℝ))
    let Gp:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k ρ 0 ν ((h:ℝ)-(s:ℝ))
    let Gg:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k (ρ+η) (2*(ρ+η)) ν ((h:ℝ)-(s:ℝ))
    let Gb:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k 0 0 ν ((h:ℝ)-(s:ℝ))
    ENNReal.ofReal (Env v h s k (A*ν^(-P.exponent)) ν Λ ρ χ ν ε tail η hΛ hρ hρhalf p Bcur Bword)=
      ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (ν^(-2*P.exponent))*ENNReal.ofReal (Gc^2)*Fcur ((v+s:ℝ≥0):ℝ)^χ+
      ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal (ν^(-2*P.exponent))*
        ENNReal.ofReal ((s:ℝ)^(-(1/2:ℝ))*Gp^2)*Fcur (v:ℝ)+
      ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (ν^(-2*P.exponent+2*ε))*ENNReal.ofReal (Gg^2)*Fneg hΛ hρ.le ((v+s:ℝ≥0):ℝ)+
      ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (ν^(-2*P.exponent-tail))*ENNReal.ofReal (Gb^2):=by
  intro Cf Cdim C Ccur Cpast Jt Cmom Cgood Cbad Gc Gp Gg Gb
  have hvH:v≤H:=(show v≤v+h from le_add_right le_rfl).trans hvhH
  have hqH:v+s≤H:=(add_le_add le_rfl hsh.le).trans hvhH
  have hq0:0<v+s:=lt_of_lt_of_le hs (le_add_left le_rfl)
  rw [MixedNativeInputEnergyClock.current_coe 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (v+s) hq0 hqH,
    MixedNativeInputEnergyClock.current_coe_all 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v hvH,
    MixedNativeInputEnergyClock.ennEnergy_coe 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ.le
      (v+s) hq0 hqH]
  exact NativeFourTermScale.ofReal_scaled A ν P.exponent ε tail χ Ccur Cpast Cgood Cbad
    (∫ω,‖S.second (v+s) ω-S.first (v+s) ω‖^2 ∂μ)
    (∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
    (∫ω,inputEnergy hΛ hρ.le (CU (v+s,ω)) (CV (v+s,ω)) ∂μ)
    (s:ℝ) Gc Gp Gg Gb (zero_lt_one.trans_le hν)
    (integral_nonneg (fun _=>sq_nonneg _)) (integral_nonneg (fun _=>sq_nonneg _))
    (integral_nonneg (fun _=>sq_nonneg _)) s.coe_nonneg hχ

end SHE.MixedNativeEnvelopeClock
