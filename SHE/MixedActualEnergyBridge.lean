module

public import SHE.NativeSignedDamping
public import SHE.MixedMovingEnergy
public import SHE.TimeMeasureMass
public import SHE.EnergyBridge

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedActualEnergyBridge
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



local instance actualEnergyBridge_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance actualEnergyBridge_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance actualEnergyBridge_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance actualEnergyBridge_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance actualEnergyBridge_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology

def negativeEnergy (ρ:ℝ):ℝ≥0∞:=
  NativeSignedDamping.input_energy (κ:=1) (Λ:=Λ) (ρ:=ρ) μ H fV fU
local notation "Neg" "[" ρ "]"=>negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ
local notation "Mass"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem negative_bound {ρ:ℝ} (hΛ0:0<Λ) (hρ:0≤ρ):
    Neg[ρ]≤ENNReal.ofReal (Λ^(-ρ)*(M-ell)^2)*ENNReal.ofReal (H:ℝ):=by
  calc
    _≤∫⁻s,∫⁻_ω:Ω,ENNReal.ofReal (Λ^(-ρ)*(M-ell)^2) ∂μ ∂timeMeasure H:=by
      apply lintegral_mono
      intro s
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (elliptic_negative_input_le (κ:=1) hΛ0 hρ
        (fV (s,ω)).1 (fU (s,ω)).1 (fV (s,ω)).2.1 (fU (s,ω)).2.1
        (fV (s,ω)).2.2 (fU (s,ω)).2.2)
    _=_:=by simp only [lintegral_const,measure_univ,one_mul,mul_one,timeMeasure_mass,mul_comm]

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hΛ hH hIJ₀ hIJ₁ in
/-- The actual coupled solution energy is controlled by its TRUE massive
negative coefficient-input energy. The full native signed Haar isometry,
causal clock integration, finiteness and real energy identification are
all derived for S; no stochastic-energy-model premise remains. -/
theorem global_energy {ρ:ℝ} (hΛ1:1≤Λ) (hρ:0<ρ) (hρ1:ρ<1/2):
    Neg[ρ]≠∞ ∧
    Mass≤(signedHeatSqConstant 1 ρ ell M*NativeSignedClock.constant ρ*signedDampingConstant ρ)*
      Λ^(ρ-1/2)*(Neg[ρ]).toReal:=by
  let C:=signedHeatSqConstant 1 ρ ell M*NativeSignedClock.constant ρ*signedDampingConstant ρ
  have hC:0≤C:=mul_nonneg (mul_nonneg
    (signedHeatSqConstant_nonneg (by norm_num : (0:ℝ)≤1) hρ hρ1 hM)
    (NativeSignedClock.constant_nonneg ρ)) (EnergyBridge.signedDampingConstant_pos hρ1).le
  have hF:Neg[ρ]≠∞:=ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (negative_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (zero_lt_one.trans_le hΛ1) hρ.le)
  have hfU:Measurable fU:=(S.first_coefficient.mono (predictable_le_product 𝓕)).measurable
  have hfV:Measurable fV:=(S.second_coefficient.mono (predictable_le_product 𝓕)).measurable
  have he:(∫⁻t,∫⁻ω,ENNReal.ofReal (‖S.second t ω-S.first t ω‖^2) ∂μ ∂timeMeasure H)≤
      ENNReal.ofReal (C*Λ^(ρ-1/2))*Neg[ρ]:=by
    calc
      _=∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
        ‖NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),fV (s,ω))-
          NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),fU (s,ω))‖^2)
          ∂μ ∂timeMeasure H ∂timeMeasure H:=by
        apply lintegral_congr_ae
        filter_upwards [timeMeasure_ae_mem H] with t ht
        exact MixedDampedDifferenceEnergy.point_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ S hΛ hH J hIJ₀ hIJ₁ t ht.2
      _≤_:=NativeSignedDamping.causal_energy (κ:=1) (by norm_num) hΛ1 hρ hρ1 hell hM μ H fV fU hfV hfU
  have hm:Measurable (fun p:ℝ≥0×Ω=>‖S.second p.1 p.2-S.first p.1 p.2‖^2):=
    (((S.second_predictable.sub S.first_predictable).mono (predictable_le_product 𝓕)).measurable.norm.pow_const 2)
  have hp:(∫⁻p:ℝ≥0×Ω,ENNReal.ofReal (‖S.second p.1 p.2-S.first p.1 p.2‖^2) ∂energyMeasure μ H)=
      ∫⁻t,∫⁻ω,ENNReal.ofReal (‖S.second t ω-S.first t ω‖^2) ∂μ ∂timeMeasure H:=
    lintegral_prod _ hm.ennreal_ofReal.aemeasurable
  have hi:Integrable (fun p:ℝ≥0×Ω=>‖S.second p.1 p.2-S.first p.1 p.2‖^2) (energyMeasure μ H):=by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))).mpr
    rw [hp]
    exact he.trans_lt (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF))
  have hreal:ENNReal.ofReal Mass=∫⁻t,∫⁻ω,ENNReal.ofReal (‖S.second t ω-S.first t ω‖^2) ∂μ ∂timeMeasure H:=by
    rw [MixedMovingEnergy.globalEnergy,ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ (fun _=>sq_nonneg _)),hp]
  rw [←hreal] at he
  refine ⟨hF,?_⟩
  have hb:=ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF) he
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal
    (MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S),
    ENNReal.toReal_ofReal (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hΛ1) _))] using hb

/-- The native Bessel output of the ACTUAL coefficient difference is
exactly the input energy used above, with no spatial normalization loss. -/
theorem negative_bessel {ρ:ℝ} (hΛ1:1≤Λ) (hρ:0≤ρ):
    Neg[ρ]=∫⁻t,∫⁻ω,ENNReal.ofReal
      (‖OneInputOperator.besselHalf Λ ρ hΛ1 hρ
        (CircleNormalization.push ((fV (t,ω)).1-(fU (t,ω)).1))‖^2) ∂μ ∂timeMeasure H:=by
  simp only [CircleNormalization.push_bessel_energy hΛ1 hρ]
  rfl

include hΛ hH hIJ₀ hIJ₁ in
/-- Actual unsquared energy scaling required by the master estimate. -/
theorem root_energy {ρ:ℝ} (hΛ1:1≤Λ) (hρ:0<ρ) (hρ1:ρ<1/2):
    Neg[ρ]≠∞ ∧ Real.sqrt Mass≤
      Real.sqrt (signedHeatSqConstant 1 ρ ell M*NativeSignedClock.constant ρ*signedDampingConstant ρ)*
        Λ^(ρ/2-1/4)*Real.sqrt (Neg[ρ]).toReal:=by
  have he:=global_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH J hIJ₀ hIJ₁ hΛ1 hρ hρ1
  let C:=signedHeatSqConstant 1 ρ ell M*NativeSignedClock.constant ρ*signedDampingConstant ρ
  have hC:0≤C:=mul_nonneg (mul_nonneg
    (signedHeatSqConstant_nonneg (by norm_num : (0:ℝ)≤1) hρ hρ1 hM)
    (NativeSignedClock.constant_nonneg ρ)) (EnergyBridge.signedDampingConstant_pos hρ1).le
  refine ⟨he.1,(Real.sqrt_le_sqrt he.2).trans_eq ?_⟩
  rw [Real.sqrt_mul (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hΛ1) _)),
    Real.sqrt_mul hC,EnergyBridge.sqrt_rpow_energy (zero_lt_one.trans_le hΛ1)]

end SHE.MixedActualEnergyBridge
