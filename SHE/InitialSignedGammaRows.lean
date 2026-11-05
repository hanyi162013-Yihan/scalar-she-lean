module
public import SHE.InitialSignedGammaTime
public import SHE.MixedNativeSignedGammaRows
public import SHE.MixedNativeCoefficientField

public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.InitialSignedGammaRows
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
local notation "hM"=>(hell.le.trans ((hbU 0).1.trans (hbU 0).2))
local notation "fU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "fV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second



local instance mixedNativeSignedGammaTime_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedNativeSignedGammaTime_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeSignedGammaTime_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mixedNativeSignedGammaTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeSignedGammaTime_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology


local notation "Mass"=>MixedNativeSignedGammaTime.realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

private theorem reflected (K F:ℝ→ℝ≥0∞)(T:ℝ):
    (∫⁻τ in Set.Ioc (0:ℝ) T,K τ*F (T-τ))=
      ∫⁻q in Set.Ioc (0:ℝ) T,K (T-q)*F q:=by
  have hp:MeasurePreserving (fun τ:ℝ=>T-τ)
      (volume.restrict (Set.Ioo (0:ℝ) T)) (volume.restrict (Set.Ioo (0:ℝ) T)):=by
    have hs:=((volume:Measure ℝ).measurePreserving_sub_left T).restrict_preimage
      (show MeasurableSet (Set.Ioo (0:ℝ) T) from measurableSet_Ioo)
    have he:(fun τ:ℝ=>T-τ) ⁻¹' Set.Ioo (0:ℝ) T=Set.Ioo (0:ℝ) T:=by
      ext τ
      simp only [Set.mem_preimage,Set.mem_Ioo]
      constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]
    rwa [he] at hs
  rw [←restrict_Ioo_eq_restrict_Ioc]
  have ht:=hp.lintegral_comp_emb (MeasurableEquiv.subLeft T).measurableEmbedding
    (fun q=>K (T-q)*F q)
  simpa only [sub_sub_cancel] using ht

variable (P:CanonicalCovariance.ProfileParameters)
local notation "E"=>MixedNativeSignedGammaRows.sectionEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P

/-- Actual signed trace on the initial physical terminal/current
triangle, including the native clock factor and true negative input. -/
theorem energy {ρ A:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(j:ℕ)(h:ℝ):
    (∫⁻T in Set.Ioc (0:ℝ) (min (H:ℝ) h),∫⁻τ in Set.Ioc (0:ℝ) T,
      E hL hρ A j 0 T.toNNReal τ)≤
      ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
        ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*
          ScalarHeatBandTime.massConstant P.exponent 0*(ProfileVariance.lowerConstant*P.lower)⁻¹*
            CompactMollifier.radius (j+1)^(2*P.exponent))*
              MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ:=by
  let K:=HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j
  let C:=ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))
  calc
    _≤∫⁻T in Set.Ioc (0:ℝ) (min (H:ℝ) h),∫⁻τ in Set.Ioc (0:ℝ) T,C*K τ*Mass hL hρ (T-τ):=by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with T hT
      apply lintegral_mono_ae
      have hm:∀ᵐτ∂volume.restrict (Set.Ioc (0:ℝ) T),τ∈Set.Ioo (0:ℝ) T:=by
        rw [←restrict_Ioo_eq_restrict_Ioc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [hm] with τ hτ
      have hb:T.toNNReal≤H:=by
        exact_mod_cast (show (T.toNNReal:ℝ)≤(H:ℝ) by
          rw [Real.coe_toNNReal _ hT.1.le]
          exact hT.2.trans (min_le_left _ _))
      have ht:τ∈Set.Ioo (0:ℝ) ((T.toNNReal:ℝ)-(0:ℝ≥0)):=by
        simpa only [NNReal.coe_zero,sub_zero,Real.coe_toNNReal _ hT.1.le] using hτ
      simpa only [Real.coe_toNNReal _ hT.1.le,K,C] using
        MixedNativeSignedGammaRows.section_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ j 0 T.toNNReal hb ht
    _≤∫⁻T in Set.Ioc (0:ℝ) h,∫⁻τ in Set.Ioc (0:ℝ) T,C*K τ*Mass hL hρ (T-τ):=
      lintegral_mono_set (Set.Ioc_subset_Ioc_right (min_le_right _ _))
    _=C*(∫⁻T in Set.Ioc (0:ℝ) h,∫⁻q in Set.Ioc (0:ℝ) T,K (T-q)*Mass hL hρ q):=by
      calc
        _=(∫⁻T in Set.Ioc (0:ℝ) h,C*(∫⁻τ in Set.Ioc (0:ℝ) T,K τ*Mass hL hρ (T-τ))):=by
          apply lintegral_congr
          intro T
          simp only [mul_assoc]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _=C*(∫⁻T in Set.Ioc (0:ℝ) h,∫⁻τ in Set.Ioc (0:ℝ) T,K τ*Mass hL hρ (T-τ)):=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _=_:=by simp_rw [reflected]
    _≤_:=by
      have hb:=InitialSignedGammaTime.energy (A:=A) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        hL hρ P.exponent_le_one (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos) j h
      simpa only [C,K,mul_assoc] using mul_le_mul_right hb C
end SHE.InitialSignedGammaRows
