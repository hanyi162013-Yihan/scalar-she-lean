module
public import SHE.ActualTerminalReconstructionEnergy

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.ActualTerminalRMS
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

local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable (D:SmoothApproximation.ScalarData)(n:ℕ)
variable (hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)
local notation "Mixed"=>ActualTerminalReconstruction.mixed
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ
local instance :SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local notation "hUp"=>(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
local notation "hVp"=>(S.second_predictable.mono (predictable_le_product 𝓕)).measurable

local notation "Low"=>MixedNativeLowBandEnergy.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ.le
local notation "Terminal"=>ActualTerminalReconstruction.terminal
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ

local notation "Remainder"=>ActualTerminalReconstructionEnergy.remainder
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ
local notation "Err"=>ActualTerminalReconstructionEnergy.error D n

private theorem rms_eq {f:ℝ≥0×Ω→CircleL2}(hf:AEStronglyMeasurable f (energyMeasure μ H))
    (hi:Integrable (fun z=>‖f z‖^2) (energyMeasure μ H)):
    Real.sqrt (∫z,‖f z‖^2 ∂energyMeasure μ H)=(eLpNorm f 2 (energyMeasure μ H)).toReal:=by
  let hm:MemLp f 2 (energyMeasure μ H):=(memLp_two_iff_integrable_sq_norm hf).mpr hi
  have he:(∫z,‖f z‖^2 ∂energyMeasure μ H)=‖hm.toLp f‖^2:=by
    rw [realLp_norm_sq]
    exact integral_congr_ae (hm.coeFn_toLp.mono (fun z hz=>congrArg (fun e:CircleL2=>‖e‖^2) hz.symm))
  rw [he,Real.sqrt_sq (norm_nonneg _),Lp.norm_toLp]

private theorem rms_three(F L G R:ℝ≥0×Ω→CircleL2)
    (hF:Measurable F)(hL:Measurable L)(hG:Measurable G)(hR:Measurable R)
    (hiF:Integrable (fun z=>‖F z‖^2) (energyMeasure μ H))
    (hiL:Integrable (fun z=>‖L z‖^2) (energyMeasure μ H))
    (hiG:Integrable (fun z=>‖G z‖^2) (energyMeasure μ H))
    (hiR:Integrable (fun z=>‖R z‖^2) (energyMeasure μ H)) (he:F=L+G+R):
    Real.sqrt (∫z,‖F z‖^2 ∂energyMeasure μ H)≤
      Real.sqrt (∫z,‖L z‖^2 ∂energyMeasure μ H)+
      Real.sqrt (∫z,‖G z‖^2 ∂energyMeasure μ H)+
      Real.sqrt (∫z,‖R z‖^2 ∂energyMeasure μ H):=by
  have mL:MemLp L 2 (energyMeasure μ H):=(memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mpr hiL
  have mG:MemLp G 2 (energyMeasure μ H):=(memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr hiG
  have mR:MemLp R 2 (energyMeasure μ H):=(memLp_two_iff_integrable_sq_norm hR.aestronglyMeasurable).mpr hiR
  have hb:eLpNorm F 2 (energyMeasure μ H)≤eLpNorm L 2 (energyMeasure μ H)+
      eLpNorm G 2 (energyMeasure μ H)+eLpNorm R 2 (energyMeasure μ H):=by
    rw [he]
    exact (eLpNorm_add_le (f:=L+G) (g:=R) (μ:=energyMeasure μ H)
      (by norm_num:(1:ENNReal)≤2)).trans
      (add_le_add (eLpNorm_add_le (f:=L) (g:=G) (μ:=energyMeasure μ H)
        (by norm_num:(1:ENNReal)≤2)) (le_refl _))
  have hfin:(eLpNorm L 2 (energyMeasure μ H)+eLpNorm G 2 (energyMeasure μ H)+
      eLpNorm R 2 (energyMeasure μ H))≠⊤:=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨mL.eLpNorm_ne_top,mG.eLpNorm_ne_top⟩,mR.eLpNorm_ne_top⟩
  have hh:=ENNReal.toReal_mono hfin hb
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨mL.eLpNorm_ne_top,mG.eLpNorm_ne_top⟩) mR.eLpNorm_ne_top,
    ENNReal.toReal_add mL.eLpNorm_ne_top mG.eLpNorm_ne_top,
    ←rms_eq μ H hF.aestronglyMeasurable hiF,←rms_eq μ H hL.aestronglyMeasurable hiL,
    ←rms_eq μ H hG.aestronglyMeasurable hiG,←rms_eq μ H hR.aestronglyMeasurable hiR] at hh
  exact hh

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁

/-- Actual finite comparison consumer for the TRUE mixed negative energy.
The low block is bounded by actual global solution energy internally;
only the finite stochastic terminal-prefix moment, supplied by the
seven-piece comparison, remains an explicit quantitative input. -/
theorem reconstruct(hUeq:aU=D.residualCoefficient)(hVeq:aV=D.smoothCoefficient n)
    (hβ:D.beta<1)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)(J0 L:ℕ)
    (hiT:Integrable (fun z=>‖∑r∈Finset.range L,Terminal (J0+r) z‖^2) (energyMeasure μ H)):
    Real.sqrt (Neg).toReal≤
      ((ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*
        LowBands.lowBandConstant D.beta)*Λ^(-ρ/2))*((2:ℝ)^J0)^(1-D.beta)*
        Real.sqrt (MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)+
      Real.sqrt (∫z,‖∑r∈Finset.range L,Terminal (J0+r) z‖^2 ∂energyMeasure μ H)+Err J0 L:=by
  have hF:=ActualTerminalNegativeInput.mixed_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ
  have hiF:=ActualTerminalNegativeInput.mixed_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ hUeq hVeq
  have hLow:=((MixedNativeLowBandEnergy.value_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ.le J0).mono
      (predictable_le_product 𝓕)).measurable
  have hiLow:=MixedNativeLowBandEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ.le J hIJ₀ hIJ₁ hβ hH B hBDG J0
  have hT:Measurable (fun z=>∑r∈Finset.range L,Terminal (J0+r) z):=
    Finset.measurable_sum _ (fun r _=>ActualTerminalBandField.measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (D.smooth_boundedSmooth n) (J0+r) hL hρ)
  have hR:=ActualTerminalReconstructionEnergy.measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J0 L
  have hiR:=ActualTerminalReconstructionEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J0 L
  have herr:0≤Err J0 L:=add_nonneg (ScalarApproximationDiscrepancy.scalarError_nonneg D n)
    (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg D.holderConstant_nonneg
      (GaussianAudit.gaussianAbsMoment_nonneg D.beta))) (Real.rpow_nonneg (CompactMollifier.radius_pos _).le _))
  have hr:Real.sqrt (∫z,‖Remainder J0 L z‖^2 ∂energyMeasure μ H)≤Err J0 L:=by
    have hb:(∫z,‖Remainder J0 L z‖^2 ∂energyMeasure μ H)≤(Err J0 L)^2:=
      hiR.2.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hH (sq_nonneg (Err J0 L)))
    have hh:=Real.sqrt_le_sqrt hb
    simpa only [Real.sqrt_sq herr] using hh
  have hsum:=rms_three μ H Mixed (Low J0) (fun z=>∑r∈Finset.range L,Terminal (J0+r) z)
    (Remainder J0 L) hF hLow hT hR hiF hiLow.1 hiT hiR.1 (by
      funext z
      simp only [Pi.add_apply,ActualTerminalReconstructionEnergy.remainder]
      abel)
  have hlow:=MixedNativeLowBandEnergy.root_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ.le J hIJ₀ hIJ₁ hβ hH B hBDG J0
  rw [←ActualTerminalReconstructionEnergy.negative_real
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ hUeq hVeq] at hsum
  linarith only [hsum,hlow,hr]

end SHE.ActualTerminalRMS
