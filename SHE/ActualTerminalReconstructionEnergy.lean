module
public import SHE.ActualTerminalNegativeInput

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.ActualTerminalReconstructionEnergy
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

def error(J m:ℕ):ℝ:=ScalarApproximationDiscrepancy.scalarError D n+
  2*(D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta)*CompactMollifier.radius (J+m)^D.beta

def remainder(J m:ℕ)(z:ℝ≥0×Ω):CircleL2:=Mixed z-Low J z-
  ∑r∈Finset.range m,Terminal (J+r) z
local notation "Remainder"=>remainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ

theorem measurable(J m:ℕ):Measurable (Remainder J m):=by
  have hm(j:ℕ):Measurable (Terminal j):=ActualTerminalBandField.measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (D.smooth_boundedSmooth n) j hL hρ
  exact ((ActualTerminalNegativeInput.mixed_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ).sub
      ((MixedNativeLowBandEnergy.value_predictable
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ.le J).mono
          (predictable_le_product 𝓕)).measurable).sub
            (Finset.measurable_sum (Finset.range m) (fun r _=>hm (J+r)))

/-- Actual global L2 remainder for finite reconstruction. Its complete
budget is uniform in the coupled states and is chosen before n. -/
theorem energy(J m:ℕ):
    Integrable (fun z=>‖Remainder J m z‖^2) (energyMeasure μ H) ∧
      (∫z,‖Remainder J m z‖^2 ∂energyMeasure μ H)≤(error D n J m)^2*(H:ℝ):=by
  haveI :IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  have hm:=(measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J m).norm.pow_const 2
  have hb(z:ℝ≥0×Ω):‖Remainder J m z‖^2≤(error D n J m)^2:=
    pow_le_pow_left₀ (norm_nonneg _) (ActualTerminalReconstruction.mixed_reconstruction
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J m z) 2
  have hi:Integrable (fun z=>‖Remainder J m z‖^2) (energyMeasure μ H):=
    (integrable_const ((error D n J m)^2)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun z=>by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hb z))
  refine ⟨hi,?_⟩
  have hmass:((energyMeasure μ H) Set.univ).toReal=(H:ℝ):=by
    change (((timeMeasure H).prod μ) Set.univ).toReal=(H:ℝ)
    rw [←Set.univ_prod_univ,Measure.prod_prod,timeMeasure_mass,measure_univ,mul_one]
    exact ENNReal.toReal_ofReal H.2
  calc
    _≤∫_z:ℝ≥0×Ω,(error D n J m)^2 ∂energyMeasure μ H:=
      integral_mono hi (integrable_const _) hb
    _=_:=by rw [integral_const];simp only [Measure.real,hmass,smul_eq_mul];ring

/-- The true original negative energy has its genuine ordinary integral,
so real RMS estimates can be used without extended-real defaults. -/
theorem negative_real(hUeq:aU=D.residualCoefficient)(hVeq:aV=D.smoothCoefficient n):
    (Neg).toReal=∫z,‖Mixed z‖^2 ∂energyMeasure μ H:=by
  rw [ActualTerminalNegativeInput.negative_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ hUeq hVeq,
    ←ofReal_integral_eq_lintegral_ofReal (ActualTerminalNegativeInput.mixed_integrable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ hUeq hVeq)
        (ae_of_all _ (fun _=>sq_nonneg _)),ENNReal.toReal_ofReal (integral_nonneg (fun _=>sq_nonneg _))]

end SHE.ActualTerminalReconstructionEnergy
