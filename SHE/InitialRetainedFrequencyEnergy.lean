module

public import SHE.InitialRetainedTriangleEnergy
public import SHE.PairedBudgetFrequency
public import SHE.FrequencyTimeInflation
public import SHE.InitialNativeSpatialFields
public import SHE.InitialRetainedSectionEnergy
public import SHE.InitialNativeClock
public import SHE.InitialActualConvolution
public import SHE.MixedTerminalEnergySplit
public import SHE.InitialActualRMSEnvelope
public import SHE.InitialRMSGapEnvelope
public import SHE.InitialTerminalFibre
public import SHE.ZeroDirectionProfile
public import SHE.MixedNativePairInitial
public import SHE.ControlledScalarReference
public import SHE.RelativePairedCurrent
public import SHE.PairedFamilyFields
public import SHE.MovingNativeFields
public import SHE.ShiftedHistoryMeasure
public import SHE.MixedPairedMovingSection
public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.MixedPastTerminalPairedLinearEnergy
public import SHE.MixedPairedCurrentClock
public import SHE.MixedPastTerminalTimeFields
public import SHE.ControlledTerminalRMSMass
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.InitialRetainedFrequencyEnergy
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance initialRetainedFrequencyEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialRetainedFrequencyEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance initialRetainedFrequencyEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance initialRetainedFrequencyEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance initialRetainedFrequencyEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance initialRetainedFrequencyEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance initialRetainedFrequencyEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance initialRetainedFrequencyEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialRetainedFrequencyEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialRetainedFrequencyEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance initialRetainedFrequencyEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance initialRetainedFrequencyEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth CutoffWordLevel
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient) (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (embed u₀,0)
local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "ZZ" T:max=>ControlledScalarReference.observations T
local notation "K" α:max T:max=>ControlledReferenceFamilyLevel.level P P.coefficient haP Λ α 0 T bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (embed u₀,0)
local notation "Zero" T:max=>ControlledReferenceFamilyLevel.level P P.coefficient haP Λ 0 0 T bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (0,0)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "RT" T:max=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
  (v:=0) (b:=T) (hvb:=bot_le) (Z:=ZZ T) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
  (F:=F) (hF:=hF) (hFm:=hFm)
local notation "En" T:max=>MixedPastTerminalTimeFields.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 T bot_le (ZZ T)
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Mglobal"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "Field"=>InitialRetainedTriangleEnergy.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

include hIJ₀ hIJ₁ in
/-- The complete initial output triangle, retaining native x, has the
same fixed-N frequency/time gain as the complete moving windows. -/
theorem actual_frequency_energy
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hh:0<h) (hhH:h≤H)
    (hspan:(h:ℝ)≤P.horizon)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0<χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov)
    {η:ℝ} (hη:0<η):
    let Cp:=PairedBudgetFrequency.constant P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) χ η order B0
    let νT:=volume.restrict (Ioc (0:ℝ) (h:ℝ))
    Integrable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2)
      (νT.prod (μ.prod AddCircle.haarAddCircle)) ∧
      (∫z:ℝ×(Ω×HeatCircle),|Field (k+1) z.1 z.2|^2 ∂νT.prod (μ.prod AddCircle.haarAddCircle))≤
        4*Cp^2*A0^2*(1+ν)^(2*(χ+η))*(h:ℝ)^((((k+1:ℕ):ℝ)*P.exponent-χ-η)/2)*
          Mglobal^χ*(H:ℝ)^(1-χ):=by
  intro Cp νT
  let ν':=FrequencyTimeInflation.inflate (h:ℝ) ν
  have hs1:(h:ℝ)≤1:=((show (h:ℝ)≤(H:ℝ) from hhH).trans hH)
  have hνν':ν≤ν':=FrequencyTimeInflation.le_inflate (show 0<(h:ℝ) from hh) hs1 hν
  have hν':0≤ν':=hν.trans hνν'
  have hj':∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν'^j:=by
    intro x j hj z
    exact (hjet x j hj z).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hν hνν' j) hA0)
  have he:=InitialRetainedTriangleEnergy.actual_product_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm J hIJ₀ hIJ₁
    hlocal hΛ hH hh hhH hspan hsmallP k hsmall hA0 hν' hχ hχβ hj'
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  let B:=PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower)
    (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν' order B0
  have hB:0≤B:=by
    have hi:=InitialRMSGapEnvelope.kernel_integral (κ:=κ) (M:=M) P
      (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
      (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) (show 0<(h:ℝ) from hh) hχ.le hχβ hA0 hν' order B0
    exact (integral_nonneg (fun d=>InitialRMSGapEnvelope.kernel_nonneg (κ:=κ) (M:=M) (χ:=χ) P
      (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
      (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) h.2 hA0 hν' order B0 d)).trans hi.2
  have hb:=PairedBudgetFrequency.total_band_bound P hκ.le
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ControlledOldIntervals.fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1) (k+1)
    (show 0<(h:ℝ) from hh) hs1 hχ.le hη hA0 hν'
    (FrequencyTimeInflation.native_band (show 0<(h:ℝ) from hh) hν) order B0
  change B≤A0*Cp*(1+ν')^(χ+η)*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/4) at hb
  have hsq:B^2≤(A0*Cp*(1+ν')^(χ+η)*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/4))^2:=
    (sq_le_sq₀ hB (hB.trans hb)).mpr hb
  have hrν:((1+ν')^(χ+η))^2=(1+ν')^(2*(χ+η)):=by
    rw [←Real.rpow_mul_natCast (show 0≤1+ν' by positivity)]
    congr 1
    ring
  have hrh:((h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/4))^2=(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/2):=by
    calc
      _=(h:ℝ)^((((k+1:ℕ):ℝ)*P.exponent/4)*(2:ℕ)):=
        (Real.rpow_mul_natCast (show 0≤(h:ℝ) from h.2) (((k+1:ℕ):ℝ)*P.exponent/4) 2).symm
      _=_:=by congr 1;ring
  have hm:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num:(0:ℝ)≤4))
      (Real.rpow_nonneg (MixedMovingEnergy.globalEnergy_nonneg
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) χ))
    (Real.rpow_nonneg H.2 (1-χ))
  refine ⟨he.1,he.2.trans (hm.trans_eq ?_)⟩
  rw [mul_pow,mul_pow,mul_pow,hrν,hrh]
  have hw:=FrequencyTimeInflation.weight_identity (show 0<(h:ℝ) from hh) hν
    (χ+η) (((k+1:ℕ):ℝ)*P.exponent/2)
  have hwe:(1+ν')^(2*(χ+η))*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/2)=
      (1+ν)^(2*(χ+η))*(h:ℝ)^((((k+1:ℕ):ℝ)*P.exponent-χ-η)/2):=by
    convert! hw using 1 <;> ring
  have hwf:=congrArg (fun a:ℝ=>4*Cp^2*A0^2*a*Mglobal^χ*(H:ℝ)^(1-χ)) hwe
  convert! hwf using 1 <;> ring_nf <;> rfl

end SHE.InitialRetainedFrequencyEnergy
