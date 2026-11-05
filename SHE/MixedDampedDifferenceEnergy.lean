module

public import SHE.MixedDampedDifferenceInput
public import SHE.LpEnergy
public import SHE.HaarDamping

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedDampedDifferenceEnergy
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
variable {Ω : Type*} [MeasurableSpace Ω]
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


local notation "R" "[" q "," hq "]"=>MixedDampedDifferenceInput.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq

theorem input_ae (q:ℝ≥0) (hq:q≤H):
    R[q,hq]=ᵐ[energyMeasure μ H] fun p=>Real.exp (-Λ*((q:ℝ)-(p.1:ℝ))) •
      (kernel ell M hell ((q:ℝ)-(p.1:ℝ),fV p)-kernel ell M hell ((q:ℝ)-(p.1:ℝ),fU p)):=by
  filter_upwards [S.controlled_residual_kernel q hq,
    MixedDampedDifferenceInput.first_input_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq,
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub (S.controlledResidualInput q)
      (MixedDampedDifferenceInput.first_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq))]
      with p hv hu hs
  change R[q,hq] p=_ at hs ⊢
  rw [hs]
  change S.controlledResidualInput q p-
    MixedDampedDifferenceInput.first_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq p=_
  rw [hv,hu,smul_sub]

/-- Exact native-clock signed column trace; no finite Haar cutoff. -/
theorem native_kernel_trace {τ:ℝ} (hτ:0<τ) (f g:EllipticField ell M):
    ‖kernel ell M hell (τ,f)-kernel ell M hell (τ,g)‖^2=
      globalSignedHeatEnergy f.1 g.1 (τ/timeScale):=by
  simp only [kernel]
  rw [RealHaarIntegrand.kernel_difference_norm_sq,
    HaarHeatIntegrand.kernel_difference_norm_sq hell (div_pos hτ timeScale_pos)]
  rfl

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ hΛ hH in
/-- Exact squared stochastic energy of the ACTUAL controlled difference,
with all original columns and physical damping retained. -/
theorem point_energy (q:ℝ≥0) (hq:q≤H):
    (∫⁻ω,ENNReal.ofReal (‖S.second q ω-S.first q ω‖^2) ∂μ)=
      ∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*Λ*((q:ℝ)-(s:ℝ)))*
        ‖kernel ell M hell ((q:ℝ)-(s:ℝ),fV (s,ω))-
          kernel ell M hell ((q:ℝ)-(s:ℝ),fU (s,ω))‖^2) ∂μ ∂timeMeasure H:=by
  have hrep:=MixedDampedDifferenceInput.representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    hΛ hH J hIJ₀ hIJ₁ q hq
  calc
    _=∫⁻ω,ENNReal.ofReal (‖I₁.integral (R[q,hq]) ω‖^2) ∂μ:=
      lintegral_congr_ae (hrep.mono (fun ω hω=>congrArg (fun X:RealL2=>ENNReal.ofReal (‖X‖^2)) hω))
    _=ENNReal.ofReal (‖I₁.integral (R[q,hq])‖^2):=(LpEnergy.lintegral_energy _).symm
    _=∫⁻s,∫⁻ω,ENNReal.ofReal (‖R[q,hq] (s,ω)‖^2) ∂μ ∂timeMeasure H:=I₁.isometry_energy _
    _=_:=by
      apply lintegral_congr_ae
      filter_upwards [Measure.ae_ae_of_ae_prod (input_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hH q hq)] with s hs
      apply lintegral_congr_ae
      filter_upwards [hs] with ω hω
      rw [hω,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
      congr 2
      rw [pow_two,←Real.exp_add]
      congr 1
      ring

end SHE.MixedDampedDifferenceEnergy
