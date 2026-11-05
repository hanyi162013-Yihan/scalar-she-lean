module

public import SHE.MixedPastTerminalRemainderEnergy
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

namespace SHE.InitialRetainedTriangleEnergy
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance initialRetainedTriangleEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialRetainedTriangleEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance initialRetainedTriangleEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance initialRetainedTriangleEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance initialRetainedTriangleEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance initialRetainedTriangleEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance initialRetainedTriangleEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance initialRetainedTriangleEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialRetainedTriangleEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialRetainedTriangleEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance initialRetainedTriangleEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance initialRetainedTriangleEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

def clippedTime (h:ℝ≥0) (T:ℝ):Icc (0:ℝ) (h:ℝ):=
  ⟨ClippedCovariance.clip 0 h T,ClippedCovariance.clip_mem h.2 T⟩

theorem clippedTime_measurable (h:ℝ≥0):Measurable (clippedTime h):=
  ((ClippedCovariance.continuous_clip 0 h).measurable).subtype_mk

def field (k:ℕ) (T:ℝ) (y:Ω×HeatCircle):ℝ:=
  if 0<T ∧ T≤(h:ℝ) then InitialNativeSpatialFields.value
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k (clippedTime h T) y else 0

local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem field_measurable (k:ℕ):Measurable (fun z:ℝ×(Ω×HeatCircle)=>Field k z.1 z.2):=by
  have hm:Measurable (fun z:ℝ×(Ω×HeatCircle)=>InitialNativeSpatialFields.value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k (clippedTime h z.1) z.2):=by
    convert! (InitialNativeSpatialFields.value_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k).comp
      (((clippedTime_measurable h).comp measurable_fst).prodMk measurable_snd) using 1
  exact hm.ite ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)) measurable_const

include hIJ₀ hIJ₁ in
/-- The ACTUAL complete scalar Word remainder on the initial output
triangle has genuine time/sample L2 energy. Its TRUE current energy is
counted once; the SAME finite old-gap budget appears squared. -/
theorem actual_product_energy
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
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov):
    let Budget:=PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν order B0
    let νT:=volume.restrict (Ioc (0:ℝ) (h:ℝ))
    Integrable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2) (νT.prod (μ.prod AddCircle.haarAddCircle)) ∧
      (∫z:ℝ×(Ω×HeatCircle),|Field (k+1) z.1 z.2|^2 ∂νT.prod (μ.prod AddCircle.haarAddCircle))≤
        4*Budget^2*Mglobal^χ*(H:ℝ)^(1-χ):=by
  intro Budget νT
  let G:=MovingPastFractional.powerWindow (H:ℝ) χ Ee
  let Bound:=4*Budget^2*Mglobal^χ*(H:ℝ)^(1-χ)
  have hEe:=MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hB:0≤Budget:=by
    have hi:=InitialRMSGapEnvelope.kernel_integral (κ:=κ) (M:=M) P
      (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
      (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) (show 0<(h:ℝ) from hh) hχ.le hχβ hA0 hν order B0
    exact (integral_nonneg (fun d=>InitialRMSGapEnvelope.kernel_nonneg (κ:=κ) (M:=M) (χ:=χ) P
      (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (PhysicalScoreChain.uniformConstant 1)
      (fun j=>(PhysicalScoreChain.uniformConstant_pos 1 j).le) (k+1) h.2 hA0 hν order B0 d)).trans hi.2
  have hnested:(∫⁻T in Ioc (0:ℝ) (h:ℝ),∫⁻y:Ω×HeatCircle,ENNReal.ofReal (|Field (k+1) T y|^2) ∂μ.prod AddCircle.haarAddCircle)≤
      ENNReal.ofReal (4*Budget)*
        (∫⁻T in Ioc (0:ℝ) (h:ℝ),∫⁻t:Fin (k+1)→ℝ,
          ENNReal.ofReal ((RT T.toNNReal) (k+1) t ν χ A0 order B0)*G (OrderedGapCoordinates.boundary T (k+1) t)
          ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) T))):=by
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with T hT
    have hcoe:(T.toNNReal:ℝ)=T:=Real.coe_toNNReal _ hT.1.le
    have hTh:T.toNNReal≤h:=Real.toNNReal_le_iff_le_coe.mpr hT.2
    have hTN:0<T.toNNReal:=by exact_mod_cast (show 0<(T.toNNReal:ℝ) from by simpa only [hcoe] using hT.1)
    let Ts:Icc (0:ℝ) (h:ℝ):=⟨T,⟨hT.1.le,hT.2⟩⟩
    have hcap:clippedTime h T=Ts:=Subtype.ext (ClippedCovariance.clip_eq ⟨hT.1.le,hT.2⟩)
    have he:(fun y:Ω×HeatCircle=>InitialRetainedSectionEnergy.wordValue
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP F hF hFm h T.toNNReal (k+1) y)=ᵐ[μ.prod AddCircle.haarAddCircle]
        fun y:Ω×HeatCircle=>Field (k+1) T y:=by
      have hf:∀ᵐy:Ω×HeatCircle ∂μ.prod AddCircle.haarAddCircle,
          ∀T:Icc (0:ℝ) (h:ℝ),∀k:ℕ,∀x:HeatCircle,
          HistoryProductMeasure.rootAverage
            (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (0,0)) k
            (fun a=>MixedPastTerminalEndpointWord.wordDifference
              𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 (⟨T,T.2.1⟩:ℝ≥0) bot_le
              (ZZ (⟨T,T.2.1⟩:ℝ≥0)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k a.2 a.1) (y.1,x)=
            InitialNativeSpatialFields.value
              𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k T (y.1,x):=
        (measurePreserving_fst (μ:=μ) (ν:=AddCircle.haarAddCircle)).quasiMeasurePreserving.ae
          (InitialNativeSpatialFields.value_initial_ae
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm)
      filter_upwards [hf] with y hy
      have hw:=hy Ts (k+1) y.2
      have hTT:0<T ∧ T≤(h:ℝ):=⟨hT.1,hT.2⟩
      have hField:Field (k+1) T y=InitialNativeSpatialFields.value
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm (k+1) Ts y:=by
        dsimp only [field]
        simp only [if_pos hTT,hcap]
      rw [hField]
      have hNN:T.toNNReal=(⟨(Ts:ℝ),Ts.2.1⟩:ℝ≥0):=Subtype.ext hcoe
      have hwN:=congrArg (fun a:ℝ≥0=>InitialRetainedSectionEnergy.wordValue
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP F hF hFm h a (k+1) y) hNN
      apply hwN.trans
      convert! hw using 1
    have hs:=InitialRetainedSectionEnergy.actual_section
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm J hIJ₀ hIJ₁
      hlocal hΛ hH T.toNNReal hTN hTh hhH hspan hsmallP k hsmall hA0 hν hχ hχβ hjet
      order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
    let η:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) T))
    have hηeq:Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) (T.toNNReal:ℝ)))=η:=
      congrArg (fun r:ℝ=>Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) r))) hcoe
    let A:=fun t:Fin (k+1)→ℝ=>(RT T.toNNReal) (k+1) t ν χ A0 order B0
    let E:=fun t:Fin (k+1)→ℝ=>(En T.toNNReal) (k+1) t
    have hA0'(t):0≤A t:=MixedPastTerminalRMS.amplitude_nonneg
      (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=T.toNNReal) (hvb:=bot_le)
      (Z:=ZZ T.toNNReal) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
      (F:=F) (hF:=hF) (hFm:=hFm) (k+1) t ν χ A0 order B0
    have hAi:Integrable A η:=by
      have hi:=MixedPastTerminalRMS.amplitude_integrable
        (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=T.toNNReal) (hvb:=bot_le)
        (Z:=ZZ T.toNNReal) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
        (F:=F) (hF:=hF) (hFm:=hFm) hTN k hA0 hν hχ.le hχβ order B0
      simpa only [NNReal.coe_zero,hηeq] using hi
    have hEm:Measurable E:=MixedPastTerminalTimeFields.currentEnergy_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 T.toNNReal bot_le (ZZ T.toNNReal)
        (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (k+1)
    have hAm:Measurable A:=MixedPastTerminalRMS.amplitude_measurable
      (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=T.toNNReal) (hvb:=bot_le)
      (Z:=ZZ T.toNNReal) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
      (F:=F) (hF:=hF) (hFm:=hFm) (k+1) ν χ A0 order B0
    have hE0(t):0≤E t:=integral_nonneg (fun _=>sq_nonneg _)
    have hEc(t):E t≤MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M:=
      MixedPastTerminalTimeFields.currentEnergy_cap
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP 0 T.toNNReal bot_le
        (ZZ T.toNNReal) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hΛ hH (hTh.trans hhH) B1 hBDG1 (k+1) t
    have hWi:Integrable (fun t=>A t*(E t)^χ) η:=by
      apply (hAi.mul_const ((MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M)^χ)).mono'
        ((hAm.mul (hEm.pow_const χ)).aestronglyMeasurable)
      apply ae_of_all
      intro t
      change ‖A t*(E t)^χ‖≤A t*(MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M)^χ
      rw [Real.norm_of_nonneg (mul_nonneg (hA0' t) (Real.rpow_nonneg (hE0 t) _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hE0 t) (hEc t) hχ.le) (hA0' t)
    have hsec:Integrable (fun y:Ω×HeatCircle=>|Field (k+1) T y|^2) (μ.prod AddCircle.haarAddCircle) ∧
        (∫y:Ω×HeatCircle,|Field (k+1) T y|^2 ∂μ.prod AddCircle.haarAddCircle)≤4*Budget*(∫t,A t*(E t)^χ ∂η):=by
      have he2:=he.mono (fun ω hω=>congrArg (fun r:ℝ=>|r|^2) hω)
      refine ⟨hs.1.congr he2,?_⟩
      rw [←integral_congr_ae he2]
      simpa only [hηeq] using hs.2
    rw [←ofReal_integral_eq_lintegral_ofReal hsec.1 (ae_of_all _ (fun _=>sq_nonneg _))]
    calc
      _≤ENNReal.ofReal (4*Budget*(∫t,A t*(E t)^χ ∂η)):=ENNReal.ofReal_le_ofReal hsec.2
      _=ENNReal.ofReal (4*Budget)*(∫⁻t,ENNReal.ofReal (A t)*G (OrderedGapCoordinates.boundary T (k+1) t) ∂η):=by
        rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hB),ofReal_integral_eq_lintegral_ofReal hWi
          (ae_of_all _ (fun t=>mul_nonneg (hA0' t) (Real.rpow_nonneg (hE0 t) _)))]
        congr 1
        apply lintegral_congr
        intro t
        rw [ENNReal.ofReal_mul (hA0' t)]
        have hp:=InitialNativeClock.rms_current_product
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP F hF hFm
          T.toNNReal (hTh.trans hhH) k t χ A0 ν hχ.le order B0
        have hg: G (OrderedGapCoordinates.boundary (T.toNNReal:ℝ) (k+1) t)=
            G (OrderedGapCoordinates.boundary T (k+1) t):=
          congrArg (fun r:ℝ=>G (OrderedGapCoordinates.boundary r (k+1) t)) hcoe
        exact hp.trans (congrArg (fun r:ℝ≥0∞=>ENNReal.ofReal (A t)*r) hg)
  have hc:=InitialActualConvolution.energy_bound P haP Λ κ M F hF hFm Ee hEe
    (show 0<(h:ℝ) from hh) (show (h:ℝ)≤(H:ℝ) from by exact_mod_cast hhH) hχ.le hχβ hA0 hν k order B0
  rw [MixedMovingEnergy.real_mass_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B1 hBDG1] at hc
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hbound:0≤Bound:=by dsimp only [Bound];positivity
  have ht:(∫⁻T in Ioc (0:ℝ) (h:ℝ),∫⁻y:Ω×HeatCircle,ENNReal.ofReal (|Field (k+1) T y|^2) ∂μ.prod AddCircle.haarAddCircle)≤ENNReal.ofReal Bound:=by
    apply hnested.trans
    have hm:=mul_le_mul_right hc (ENNReal.ofReal (4*Budget))
    apply hm.trans_eq
    rw [ENNReal.ofReal_rpow_of_nonneg hM hχ.le,
      ENNReal.ofReal_rpow_of_nonneg (x:=(H:ℝ)) (p:=1-χ) H.2 (sub_nonneg.mpr (hχβ.le.trans P.exponent_le_one)),
      ←ENNReal.ofReal_mul (Real.rpow_nonneg hM _),←ENNReal.ofReal_mul hB,
      ←ENNReal.ofReal_mul (mul_nonneg (by norm_num) hB)]
    congr 1
    dsimp only [Bound]
    ring
  have hm:Measurable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2):=
    (continuous_abs.measurable.comp (field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm (k+1))).pow_const 2
  have hl:(∫⁻z:ℝ×(Ω×HeatCircle),ENNReal.ofReal (|Field (k+1) z.1 z.2|^2) ∂νT.prod (μ.prod AddCircle.haarAddCircle))≤ENNReal.ofReal Bound:=by
    calc
      _=∫⁻T in Ioc (0:ℝ) (h:ℝ),∫⁻y:Ω×HeatCircle,ENNReal.ofReal (|Field (k+1) T y|^2) ∂μ.prod AddCircle.haarAddCircle:=by
        apply lintegral_prod (μ:=νT) (ν:=μ.prod AddCircle.haarAddCircle)
        convert! (ENNReal.measurable_ofReal.comp hm).aemeasurable using 1
      _≤_:=ht
  have hi:Integrable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2) (νT.prod (μ.prod AddCircle.haarAddCircle)):=by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
    exact hl.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,(ENNReal.ofReal_le_ofReal_iff hbound).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))]
  exact hl

end SHE.InitialRetainedTriangleEnergy
