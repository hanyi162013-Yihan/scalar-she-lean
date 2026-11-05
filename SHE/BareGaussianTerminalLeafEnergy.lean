module

public import SHE.FullNativeRemainderHilbertEnergy
public import SHE.FullLeafClockIdentity
public import SHE.CanonicalGaussianRootBands
public import SHE.FullRemainderConstants
public import SHE.HighFiniteRemainderWeight
public import SHE.BareGaussianRemainderDegree
public import SHE.HilbertDyadicRemainder
public import SHE.MixedNativeFullLeafHilbert
public import SHE.NativeBesselSectionEnergy
public import SHE.InitialOutputExtension
public import SHE.InitialCompleteTimePatch
public import SHE.InitialRetainedFrequencyEnergy
public import SHE.RetainedTerminalAllFrequency
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

namespace SHE.BareGaussianTerminalLeafEnergy
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance fullNativeRemainderEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance fullNativeRemainderEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance fullNativeRemainderEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance fullNativeRemainderEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance fullNativeRemainderEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance fullNativeRemainderEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullNativeRemainderEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance fullNativeRemainderEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth CutoffWordLevel
variable(P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable {a:ℝ→ℝ}(ha:BoundedSmooth a){B Hr:ℝ}(hB:∀z,|a z|≤B)(hHr:0≤Hr)
variable(hholder:∀z w,|a z-a w|≤Hr*|z-w|^P.exponent)

/-- Exact bare root used in the actual scalar comparison. -/
def root(j:ℕ):HeatCircle→WordRecursion.State 1→ℝ:=
  fun _ z=>ScalarHeatBands.band a (j+1) (z 0)

include ha in
theorem root_uniform(j:ℕ):UniformBoundedSmooth (root (a:=a) j):=
  UniformBoundedSmooth.fixed ((ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right
    (EuclideanSpace.proj (0:Fin 1)))
include ha in
theorem root_measurable(j:ℕ):Measurable (fun z:HeatCircle×WordRecursion.State 1=>root (a:=a) j z.1 z.2):=
  ((ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right
    (EuclideanSpace.proj (0:Fin 1))).smooth.continuous.measurable.comp measurable_snd

include ha hB hHr hholder in
theorem root_jets(k j:ℕ)(x:HeatCircle)(l:ℕ)(hl:l≤k+2)(z:WordRecursion.State 1):
    ‖iteratedFDeriv ℝ l (root (a:=a) j x) z‖≤
      (ScalarHeatBandBernstein.amplitude B Hr P.exponent (k+2)*
        ((2:ℝ)^(j+1))^(-P.exponent))*((2:ℝ)^(j+1))^l:=by
  have hj:=ScalarHeatRootBands.test_jets ha hB hHr P.exponent_pos.le P.exponent_le_one hholder
    (fun _:HeatCircle=>1) (W:=1) zero_le_one (fun _=>by norm_num) (k+2) (j+1) x l hl z
  have he:ScalarHeatRootBands.test a (fun _:HeatCircle=>1) (j+1) x=root (a:=a) j x:=by
    funext z
    simp only [ScalarHeatRootBands.test,root,one_mul]
  rw [he] at hj
  simpa only [one_mul] using hj

variable(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
def realField(k j:ℕ)(z:ℝ×Ω):CircleL2:=
  MixedNativeFullLeafHilbert.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
    (RemainderBandSpans.span P.exponent (j+1)) (root (a:=a) j) (root_uniform ha j)
    (root_measurable ha j) hL hρ (k+1) z

def field(k j:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  realField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha hL hρ k j ((z.1:ℝ),z.2)
local notation "RF"=>realField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha hL hρ
local notation "FF"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha hL hρ

theorem realField_measurable(k j:ℕ):Measurable (RF k j):=
  MixedNativeFullLeafHilbert.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
    (RemainderBandSpans.span P.exponent (j+1)) (root (a:=a) j) (root_uniform ha j)
    (root_measurable ha j) hL hρ (k+1)

theorem field_measurable(k j:ℕ):Measurable (FF k j):=
  (realField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP ha hL hρ k j).comp
    ((measurable_coe_nnreal_real.comp measurable_fst).prodMk measurable_snd)

/-- Definitionally the exact bare-root field already linked to the
terminal finite-expansion leaf, with its genuine individual window. -/
theorem field_eq_clock(k j:ℕ):FF k j=
    FullLeafClockIdentity.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP
      (RemainderBandSpans.span P.exponent (j+1)) j (k+1) hL ρ hρ:=rfl

variable(J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable(hIJ0:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable(hIJ1:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include hIJ0 hIJ1 hB hHr hholder in
/-- The actual native terminal leaf at prescribed finite depth has
R^-8 per-band energy. No smooth derivative enters its amplitude. -/
theorem real_energy
    (hlocal:StandardTerminalPastLocality J)(hH:(H:ℝ)≤1)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k j:ℕ)(hdepth:SHE.depth P.exponent≤k+1)
    (hJH:RemainderBandSpans.span P.exponent (j+1)≤H)
    (hJP:(RemainderBandSpans.span P.exponent (j+1):ℝ)≤P.horizon)
    (hJS:∀l,l<k+1→(RemainderBandSpans.span P.exponent (j+1):ℝ)≤PhysicalScoreChain.uniformHorizon 1 l)
    {χ η:ℝ}(hχ:0<χ)(hχβ:χ<P.exponent)(hχeq:χ=P.exponent/2)
    (hη:0<η)(hηβ:η≤P.exponent/4)(hb:P.exponent≤4/25)
    (order:ℕ)(horder:0<order)(ho0:1≤(order:ℝ)*(1-χ))(ho1:1≤(order:ℝ)*(1-χ/P.exponent))
    (B0 B1 Bcov:ℝ≥0)(hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1)(hBDGcov:StandardTerminalBDGPower (k+3) J Bcov):
    let C:=FullRemainderConstants.comparison P κ M (H:ℝ) (k+1) χ η order B0 B1 Bcov
    let A:=ScalarHeatBandBernstein.amplitude B Hr P.exponent (k+2)
    let D:=Λ^(-ρ)*C*A^2*(2:ℝ)^(2*(P.exponent/2+η))*Global^χ
    Integrable (fun z=>‖RF k j z‖^2) ((volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod μ) ∧
      (∫z,‖RF k j z‖^2 ∂((volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod μ))≤
        D*((2:ℝ)^(j+1))^(-8:ℝ):=by
  intro C A D
  let w:=RemainderBandSpans.span P.exponent (j+1)
  let ν:ℝ:=(2:ℝ)^(j+1)
  have hν:1≤ν:=one_le_pow₀ (show (1:ℝ)≤2 by norm_num)
  have hνpos:0<ν:=zero_lt_one.trans_le hν
  have hA:0≤A:=ScalarHeatBandBernstein.amplitude_nonneg hHr (k+2)
  let A0:=A*ν^(-P.exponent)
  have hA0:0≤A0:=mul_nonneg hA (Real.rpow_nonneg hνpos.le _)
  have he:=FullNativeRemainderHilbertEnergy.actual_frequency_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP w
    (root (a:=a) j) (root_uniform ha j) (root_measurable ha j) J hIJ0 hIJ1 hL hρ
    hlocal (zero_le_one.trans hL) hH (RemainderBandSpans.span_pos _ _) hJH hJP hsmallP
    k hJS hA0 hνpos.le hχ hχβ (root_jets P ha hB hHr hholder k j)
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov hη
  have hC:0≤C:=by
    unfold C FullRemainderConstants.comparison
    have hc:=MixedPastWordMoments.momentConstant_nonneg P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    positivity
  change Integrable (fun z=>‖RF k j z‖^2) _ ∧ _ at he
  have hw:A0^2*(1+ν)^(2*(χ+η))*(w:ℝ)^((((k+1:ℕ):ℝ)*P.exponent-χ-η)/2)≤
      A^2*(2:ℝ)^(2*(P.exponent/2+η))*ν^(-8:ℝ):=by
    have hweight:=BareGaussianRemainderDegree.weight (β:=P.exponent) (χ:=χ) (η:=η) hν (add_nonneg hχ.le hη.le) (k+1)
    have hdeg:=BareGaussianRemainderDegree.eight_le P.exponent_pos hb hη.le hηβ (k+1) hdepth
    have hpow:ν^(-BareGaussianRemainderDegree.degree P.exponent χ η (k+1))≤ν^(-8:ℝ):=by
      apply Real.rpow_le_rpow_of_exponent_le hν
      rw [hχeq]
      linarith
    have hw8:=hweight.trans (mul_le_mul_of_nonneg_left hpow
      (Real.rpow_nonneg (by norm_num:(0:ℝ)≤2) (2*(χ+η))))
    have hm:=mul_le_mul_of_nonneg_left hw8 (sq_nonneg A)
    change (A*ν^(-P.exponent))^2*(1+ν)^(2*(χ+η))*(ν^(-3*P.exponent))^
      ((((k+1:ℕ):ℝ)*P.exponent-χ-η)/2)≤_
    rw [hχeq] at hm
    rw [mul_pow,hχeq]
    convert! hm using 1 <;> ring
  have he2:=he.2
  simp only [show 1+k=k+1 by omega] at he2
  change (∫z,‖RF k j z‖^2 ∂((volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod μ))≤
    Λ^(-ρ)*(C*A0^2*(1+ν)^(2*(χ+η))*(w:ℝ)^((((k+1:ℕ):ℝ)*P.exponent-χ-η)/2)*Global^χ) at he2
  refine ⟨he.1,he2.trans ?_⟩
  have hm:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hL) (-ρ)) hC))
    (Real.rpow_nonneg (MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) χ)
  convert! hm using 1 <;> dsimp only [D,ν] <;> ring
end SHE.BareGaussianTerminalLeafEnergy
