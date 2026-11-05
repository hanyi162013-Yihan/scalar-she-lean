module
public import SHE.MixedPastNativeCompleteColumns
public import SHE.NativeTwoInputMajorant
public import SHE.SignedNativeBudgetMajorant

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativeBudgetMajorants
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation Real
  ControlledProfile ControlledReferenceLevel ControlledOldIntervals NativeSignedHaarProcess PhysicalScoreChain
open scoped NNReal ENNReal
local instance movingNativeBudgetMajorants_realSigma:MeasurableSpace RealL2:=borel _
local instance movingNativeBudgetMajorants_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance movingNativeBudgetMajorants_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance movingNativeBudgetMajorants_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)
local notation "CBudget"=>MixedPastNativeCompleteColumns.commonBudget
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
local notation "SBudget"=>MixedPastNativeCompleteColumns.signedBudget
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

/-- The literal complete native-column cap has four reflected terms:
actual current displacement, actual past displacement, signed negative
input, and the high-moment bad tail. No displacement supremum is used. -/
theorem four_terms (v h s:ℝ≥0)(hs:0<s)(hsh:s<h)(hh1:(h:ℝ)≤1)
    (k:ℕ)(A0 ν mass ρ χ lam ε tail η:ℝ)(hmass:1≤mass)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hlam:1≤lam)(p:ℕ)(Bcur Bword:ℝ≥0):
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
    4*(CBudget v (v+h) k (v+s) A0 ν ρ χ p Bcur Bword)^2+
      2*(SBudget v (v+h) k (v+s) A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur)^2≤
      8*A0^2*(Ccur^2*Eq^χ*Gχ^2+Cpast^2*Ev*(s:ℝ)^(-(1/2:ℝ))*G0^2)+
      4*A0^2*(Cgood^2*lam^(2*ε)*Eneg*Ggood^2+Cbad^2*lam^(-tail)*Gbad^2):=by
  intro Cf Cdim C Ccur Cpast Jt Cmom Cgood Cbad Eq Ev Eneg Gχ G0 Ggood Gbad
  have hT:0<(h:ℝ):=by exact_mod_cast hs.trans hsh
  have hsR:0<(s:ℝ):=by exact_mod_cast hs
  have hw:0<(h:ℝ)-(s:ℝ):=sub_pos.mpr (by exact_mod_cast hsh)
  have hEq:0≤Eq:=integral_nonneg (fun _=>sq_nonneg _)
  have hEv:0≤Ev:=integral_nonneg (fun _=>sq_nonneg _)
  have hE:0≤Eneg:=integral_nonneg (fun _=>sq_nonneg _)
  have hl:0<lam:=zero_lt_one.trans_le hlam
  have hd:(h:ℝ)-((h:ℝ)-(s:ℝ))=(s:ℝ):=by ring
  have hCB:CBudget v (v+h) k (v+s) A0 ν ρ χ p Bcur Bword=
      ((h:ℝ)-(s:ℝ))^(ρ/2)*(Ccur*Eq^(χ/2)*
        QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
          (h:ℝ) (s:ℝ) ((2-χ)/4) A0 ν+
        Cpast*sqrt Ev*(s:ℝ)^(-(1/4:ℝ))*
        QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
          (h:ℝ) (s:ℝ) (1/2:ℝ) A0 ν):=by
    simp only [MixedPastNativeCompleteColumns.commonBudget,NNReal.coe_add,
      add_sub_cancel_left,add_sub_add_left_eq_sub]
    rfl
  have hc:=NativeTwoInputMajorant.square_bound P (fraction P*P.lower) (uniformConstant 1)
    k (h:ℝ) ((h:ℝ)-(s:ℝ)) (s:ℝ) ρ χ ν A0 Ccur Cpast Eq Ev hT hh1 hw hsR hEq hEv
  rw [hd,←hCB] at hc
  let G:=Cgood*lam^ε*sqrt Eneg
  let B:=Cbad*lam^(-tail/2)
  have hG:0≤G:=mul_nonneg (mul_nonneg
    (PastSignedEndpointTime.goodCoefficient_nonneg P k Jt ρ η) (rpow_nonneg hl.le _)) (sqrt_nonneg _)
  have hB:0≤B:=mul_nonneg (PastSignedEndpointTime.badCoefficient_nonneg P k M Cmom)
    (rpow_nonneg hl.le _)
  have hSB:SBudget v (v+h) k (v+s) A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur=
      G*((h:ℝ)-(s:ℝ))^((ρ+η)/2)*
        QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
          (h:ℝ) (s:ℝ) (RawTraceTimeEnvelope.freshDegree ρ η) A0 ν+
      B*QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
          (h:ℝ) (s:ℝ) (1/2:ℝ) A0 ν:=by
    simp only [MixedPastNativeCompleteColumns.signedBudget,NNReal.coe_add,
      add_sub_cancel_left,add_sub_add_left_eq_sub]
    dsimp only [G,B,Cgood,Cbad,Jt,Cmom,Eneg]
    ring
  have hG2:G^2=Cgood^2*lam^(2*ε)*Eneg:=by
    dsimp only [G]
    rw [mul_pow,mul_pow,sq_sqrt hE,←rpow_mul_natCast hl.le]
    congr 2
    ring
  have hB2:B^2=Cbad^2*lam^(-tail):=by
    dsimp only [B]
    rw [mul_pow,←rpow_mul_natCast hl.le]
    congr 2
    ring
  have hb:=SignedNativeBandFrequency.budget_square_bound P (fraction P*P.lower) (uniformConstant 1)
    k ρ η (h:ℝ) A0 ν G B hT hh1 hw hG hB
  rw [hd,←hSB,hG2,hB2] at hb
  calc
    _=2*(2*(CBudget v (v+h) k (v+s) A0 ν ρ χ p Bcur Bword)^2)+
        2*(SBudget v (v+h) k (v+s) A0 ν mass ρ lam ε tail η hmass hρ hρhalf p Bcur)^2:=by ring
    _≤2*(4*A0^2*(Ccur^2*Eq^χ*Gχ^2+Cpast^2*Ev*(s:ℝ)^(-(1/2:ℝ))*G0^2))+
        2*(2*A0^2*(Cgood^2*lam^(2*ε)*Eneg*Ggood^2+Cbad^2*lam^(-tail)*Gbad^2)):=
      add_le_add (mul_le_mul_of_nonneg_left hc (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    _=_:=by ring
end SHE.MovingNativeBudgetMajorants
