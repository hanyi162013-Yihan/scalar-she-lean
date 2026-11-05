module
public import SHE.ActualTerminalReconstruction

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.ActualTerminalNegativeInput
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

theorem mixed_measurable:Measurable Mixed:=
  (OneInputOperator.besselHalf Λ ρ hL hρ.le).continuous.measurable.comp
    (CircleNormalization.push.continuous.measurable.comp
      (((ScalarApproximationDiscrepancy.smoothField_measurable D n).comp hVp).sub
        ((ScalarApproximationDiscrepancy.roughField_measurable D).comp hUp)))

private theorem coefficient_eq {f g:ℝ→ℝ}(hf:Measurable f)(hg:Measurable g)
    (A B:ℝ)(hA:∀x,|f x|≤A)(hB:∀x,|g x|≤B)(U:RealL2)(he:f=g):
    CoefficientFields.coefficient f hf A hA U=CoefficientFields.coefficient g hg B hB U:=by
  apply Lp.ext
  filter_upwards [CoefficientFields.coefficient_ae f hf A hA U,
    CoefficientFields.coefficient_ae g hg B hB U] with x hf hg
  rw [hf,hg,he]

/-- The full native mixed input is exactly the negative input from the
original stochastic energy bridge, with no smooth-smooth replacement. -/
theorem negative_eq(hUeq:aU=D.residualCoefficient)(hVeq:aV=D.smoothCoefficient n):
    Neg=∫⁻z,ENNReal.ofReal (‖Mixed z‖^2) ∂energyMeasure μ H:=by
  have hu(z:ℝ≥0×Ω):(ContinuousHeatMild.coefficientFunction haU hell hbU S.first z).1=
      ScalarApproximationDiscrepancy.roughField D (S.first z.1 z.2):=
    coefficient_eq haU D.residual_continuous.measurable M D.cap
      (NonlinearHaarIntegrand.absBound hell hbU) D.residual_abs_bound (S.first z.1 z.2) hUeq
  have hv(z:ℝ≥0×Ω):(ContinuousHeatMild.coefficientFunction haV hell hbV S.second z).1=
      ScalarApproximationDiscrepancy.smoothField D n (S.second z.1 z.2):=
    coefficient_eq haV (D.smooth_boundedSmooth n).smooth.continuous.measurable M D.cap
      (NonlinearHaarIntegrand.absBound hell hbV) (ScalarApproximationDiscrepancy.smooth_abs_bound D n)
      (S.second z.1 z.2) hVeq
  rw [MixedActualEnergyBridge.negative_bessel
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ.le]
  simp_rw [hu,hv]
  have hm:Measurable (fun z=>ENNReal.ofReal (‖Mixed z‖^2)):=
    (mixed_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ).norm.pow_const 2 |>.ennreal_ofReal
  exact (lintegral_prod _ hm.aemeasurable).symm

/-- Genuine integrability of the reconstructed mixed input is derived
from the original bounded coefficients and exact energy identity. -/
theorem mixed_integrable(hUeq:aU=D.residualCoefficient)(hVeq:aV=D.smoothCoefficient n):
    Integrable (fun z=>‖Mixed z‖^2) (energyMeasure μ H):=by
  have hm:=(mixed_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ).norm.pow_const 2
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))).mpr
  rw [←negative_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ hUeq hVeq]
  exact (MixedActualEnergyBridge.negative_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (zero_lt_one.trans_le hL) hρ.le).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

end SHE.ActualTerminalNegativeInput
