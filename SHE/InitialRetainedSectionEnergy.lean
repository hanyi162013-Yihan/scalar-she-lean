module

public import SHE.MixedPastTerminalRemainderEnergy
public import SHE.InitialNativeWordFields
public import SHE.RetainedTerminalLinearEnergy
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

namespace SHE.InitialRetainedSectionEnergy
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance initialRetainedSectionEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialRetainedSectionEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance initialRetainedSectionEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance initialRetainedSectionEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance initialRetainedSectionEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance initialRetainedSectionEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance initialRetainedSectionEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance initialRetainedSectionEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialRetainedSectionEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialRetainedSectionEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance initialRetainedSectionEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance initialRetainedSectionEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

def wordValue (window:ℝ≥0) (T:ℝ≥0) (k:ℕ) (y:Ω×HeatCircle):ℝ:=
  HistoryProductMeasure.rootAverage
    (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 T bot_le (0,0)) k
    (fun a=>MixedPastTerminalEndpointWord.wordDifference
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 T bot_le (ZZ T)
        (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k a.2 a.1) y

include hIJ₀ hIJ₁ in
/-- At the actual initial past, D0=0 removes the covariance and past
sources. The remaining true current energy stays INSIDE its original
time integral; the RMS mass uses one uniform h-envelope. -/
theorem actual_section (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
    (T:ℝ≥0) (hT:0<T) (hTh:T≤h) (hhH:h≤H) (hspan:(h:ℝ)≤P.horizon)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0<χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov):
    let η:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) (T:ℝ)))
    let Budget:=PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν order B0
    Integrable (fun y:Ω×HeatCircle=>|wordValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP F hF hFm h T (k+1) y|^2) (μ.prod AddCircle.haarAddCircle) ∧
      (∫y:Ω×HeatCircle,|wordValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP F hF hFm h T (k+1) y|^2 ∂μ.prod AddCircle.haarAddCircle)≤
        4*Budget*(∫t,(RT T) (k+1) t ν χ A0 order B0*(En T) (k+1) t^χ ∂η):=by
  intro η Budget
  have hs:=RetainedTerminalLinearEnergy.actual_linear_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP 0 T bot_le (ZZ T)
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hlocal hΛ hH hT (fun _ _=>le_rfl)
    (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)
    (by simpa only [NNReal.coe_zero,sub_zero] using ((show (T:ℝ)≤(h:ℝ) from by exact_mod_cast hTh).trans hspan))
    (hTh.trans hhH) hsmallP k (fun j hj=>by simpa only [NNReal.coe_zero,sub_zero] using
      ((show (T:ℝ)≤(h:ℝ) from by exact_mod_cast hTh).trans (hsmall j hj)))
    hA0 hν hχ hχβ hjet order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  have he0:(∫ω,‖S.second 0 ω-S.first 0 ω‖^2 ∂μ)=0:=by
    calc
      _=∫ω,(0:ℝ) ∂μ:=by
        apply integral_congr_ae
        filter_upwards [MixedNativeAdditiveResidualPair.first_zero 𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S,
          MixedNativeAdditiveResidualPair.second_zero 𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S] with ω hU hV
        rw [hU,hV,sub_self,norm_zero,zero_pow (by decide:(2:ℕ)≠0)]
      _=0:=integral_zero _ _
  dsimp only at hs
  simp only [NNReal.coe_zero,he0,Real.zero_rpow P.exponent_pos.ne',Real.zero_rpow hχ.ne',mul_zero,add_zero,zero_add] at hs
  let KK:=InitialRMSGapEnvelope.kernel P κ M (ControlledOldIntervals.fraction P*P.lower)
    (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν order B0
  have hh:0<(h:ℝ):=by exact_mod_cast hT.trans_le hTh
  have hKi:=InitialRMSGapEnvelope.kernel_integral (κ:=κ) (M:=M) P
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
    (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) hh hχ.le hχβ hA0 hν order B0
  have hK0(d):0≤KK d:=InitialRMSGapEnvelope.kernel_nonneg (κ:=κ) (M:=M) (χ:=χ) P
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
    (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) hh.le hA0 hν order B0 d
  have hg:=OrderedGapCoordinates.gaps_measurePreserving (T:ℝ) (k+1)
  have hKG:Integrable (fun t:Fin (k+1)→ℝ=>KK (OrderedGapCoordinates.gaps (T:ℝ) (k+1) t)):=
    hg.integrable_comp_of_integrable hKi.1
  have hη:η≤(volume:Measure (Fin (k+1)→ℝ)):=by
    rw [show η=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) (T:ℝ))) from rfl,
      ←Measure.restrict_pi_pi (μ:=fun _:Fin (k+1)=>(volume:Measure ℝ)) (fun _=>Ioc (0:ℝ) (T:ℝ))]
    exact Measure.restrict_le_self
  have hRTi:=MixedPastTerminalRMS.amplitude_integrable (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
    (v:=0) (b:=T) (hvb:=bot_le) (Z:=ZZ T) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
    (F:=F) (hF:=hF) (hFm:=hFm) hT k hA0 hν hχ.le hχβ order B0
  have hm:(∫t,(RT T) (k+1) t ν χ A0 order B0 ∂η)≤Budget:=by
    calc
      _≤∫t,KK (OrderedGapCoordinates.gaps (T:ℝ) (k+1) t) ∂η:=by
        apply integral_mono hRTi (hKG.mono_measure hη)
        intro t
        exact InitialActualRMSEnvelope.amplitude_bound P haP Λ T (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl)
          F hF hFm κ M hh (by exact_mod_cast hTh) hχ.le hχβ hA0 hν k t order B0
      _≤∫t,KK (OrderedGapCoordinates.gaps (T:ℝ) (k+1) t):=
        integral_mono_measure hη (ae_of_all _ (fun t=>hK0 _)) hKG
      _=∫d,KK d:=by convert! hg.integral_comp (OrderedGapCoordinates.gapEquiv (T:ℝ) (k+1)).measurableEmbedding KK using 1
      _≤Budget:=hKi.2
  have hw:0≤∫t,(RT T) (k+1) t ν χ A0 order B0*(En T) (k+1) t^χ ∂η:=by
    apply integral_nonneg
    intro t
    exact mul_nonneg (MixedPastTerminalRMS.amplitude_nonneg (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
      (v:=0) (b:=T) (hvb:=bot_le) (Z:=ZZ T) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
      (F:=F) (hF:=hF) (hFm:=hFm) (k+1) t ν χ A0 order B0) (Real.rpow_nonneg (integral_nonneg (fun _=>sq_nonneg _)) _)
  refine ⟨hs.1,?_⟩
  have hh0:=hs.2
  have hb:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num:(0:ℝ)≤4)) hw
  exact hh0.trans (by convert! hb using 1 <;> ring)

end SHE.InitialRetainedSectionEnergy
