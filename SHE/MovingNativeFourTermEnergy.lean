module
public import SHE.MovingNativeBudgetMajorants
public import SHE.MovingNativeColumnEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MovingNativeFourTermEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation Real
  ControlledProfile ControlledReferenceLevel ControlledOldIntervals NativeSignedHaarProcess PhysicalScoreChain
  SmoothCylinders UniformSmooth CutoffWordLevel
open scoped NNReal ENNReal
local instance movingNativeFourTermEnergy_realSigma:MeasurableSpace RealL2:=borel _
local instance movingNativeFourTermEnergy_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance movingNativeFourTermEnergy_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance movingNativeFourTermEnergy_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance movingNativeFourTermEnergy_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance movingNativeFourTermEnergy_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
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

/-- The four concrete reflected energy terms, retaining both actual
displacement times and the true signed coefficient negative energy. -/
def envelope (v h s:ℝ≥0)(k:ℕ)(A0 ν mass ρ χ lam ε tail η:ℝ)
    (hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)(p:ℕ)(Bcur Bword:ℝ≥0):ℝ:=
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
  let Eq:=∫ω,‖S.second (v+s) ω-S.first (v+s) ω‖^2 ∂μ
  let Ev:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
  let Eneg:=∫ω,inputEnergy hmass hρ.le (CU (v+s,ω)) (CV (v+s,ω)) ∂μ
  let Gχ:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k ρ χ ν ((h:ℝ)-(s:ℝ))
  let G0:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k ρ 0 ν ((h:ℝ)-(s:ℝ))
  let Ggood:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k
    (ρ+η) (2*(ρ+η)) ν ((h:ℝ)-(s:ℝ))
  let Gbad:=NativeCurrentBudgetFrequency.majorant P (fraction P*P.lower) (uniformConstant 1) k 0 0 ν ((h:ℝ)-(s:ℝ))
  8*A0^2*(Ccur^2*Eq^χ*Gχ^2+Cpast^2*Ev*(s:ℝ)^(-(1/2:ℝ))*G0^2)+
    4*A0^2*(Cgood^2*lam^(2*ε)*Eneg*Ggood^2+Cbad^2*lam^(-tail)*Gbad^2)
local notation "Env"=>envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P

theorem budget_le (v h s:ℝ≥0)(hs:0<s)(hsh:s<h)(hh1:(h:ℝ)≤1)
    (k:ℕ)(A0 ν mass ρ χ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(p:ℕ)(Bcur Bword:ℝ≥0):
    4*(MixedPastNativeCompleteColumns.commonBudget
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v (v+h) k (v+s) A0 ν ρ χ p Bcur Bword)^2+
    2*(MixedPastNativeCompleteColumns.signedBudget
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v (v+h)
      k (v+s) A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur)^2≤
      Env v h s k A0 ν mass ρ χ lam ε tail η hmass hρ hρhalf p Bcur Bword:=
  MovingNativeBudgetMajorants.four_terms
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
    v h s hs hsh hh1 k A0 ν mass ρ χ lam ε tail η hmass hρ hρhalf hlam p Bcur Bword

variable (haP:BoundedSmooth P.coefficient)(h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Left"=>MovingNativeColumnAverages.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Right"=>MovingNativeColumnAverages.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Actual old-time-averaged native columns obey the four reflected
sample energy bounds; no kernel moment or column bound is assumed. -/
theorem energy(k:ℕ)(hΛ:0<Λ)(hlocal:StandardTerminalPastLocality J)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hrootTarget:∀x i,(Z.observations x i).target=(h:ℝ))
    (hrootStop:∀x i,(Z.observations x i).stop=(h:ℝ))(hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(h:ℝ)≤P.horizon)
    (hspanF:(h:ℝ)≤NativeUniversalConstants.rowHorizon (1+k))
    (hspanC:(h:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega))
    (hspanS:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hHistory:∀j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (v s:ℝ≥0)(hs:0<s)(hsh:s<h)(hvhH:v+h≤H)(hH:(H:ℝ)≤1)
    (B1:ℝ≥0)(hBDG1:StandardTerminalBDGPower 1 J B1)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (p:ℕ)(hp:0<p)(Bcur:ℝ≥0)(hBDGcur:StandardTerminalBDGPower (p*(k+2)) J Bcur)
    (Bword:ℝ≥0)(hBDGword:StandardTerminalBDGPower (k+2) J Bword)
    (χ:ℝ)(hχ:0≤χ)(hχ1:χ<1)(horder:1≤(p:ℝ)*(1-χ))
    (mass ρ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(htail:tail≤ε*(2*((p-1:ℕ):ℝ)))(hη:0<η)(hρη:ρ+η<1):
    Integrable (fun ω=>‖Left hΛ.le k hmass hρ.le ((v,s),ω)‖^2) μ∧
    Integrable (fun ω=>‖Right hΛ.le k hmass hρ.le ((v,s),ω)‖^2) μ∧
      (∫ω,‖Left hΛ.le k hmass hρ.le ((v,s),ω)‖^2 ∂μ)+
        (∫ω,‖Right hΛ.le k hmass hρ.le ((v,s),ω)‖^2 ∂μ)≤
      Env v h s k A0 ν mass ρ χ lam ε tail η hmass hρ hρhalf p Bcur Bword:=by
  obtain ⟨hi0,hi1,hcap⟩:=MovingNativeColumnEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ k hΛ hlocal hsmallPoint hsmallL2
    hrootTarget hrootStop hcenter hspan hspanF hspanC hspanS hHistory
    v s hs hsh hvhH hH B1 hBDG1 A0 ν hA0 hν hjet p hp Bcur hBDGcur Bword hBDGword
    χ hχ hχ1 horder mass ρ lam ε tail η hmass hρ hρhalf hlam htail hη hρη
  have hhH:h≤H:=(show h≤v+h from le_add_left le_rfl).trans hvhH
  have hhHR:(h:ℝ)≤(H:ℝ):=by exact_mod_cast hhH
  have hh1:(h:ℝ)≤1:=hhHR.trans hH
  exact ⟨hi0,hi1,hcap.trans (budget_le
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
    v h s hs hsh hh1 k A0 ν mass ρ χ lam ε tail η hmass hρ hρhalf hlam p Bcur Bword)⟩
end SHE.MovingNativeFourTermEnergy
