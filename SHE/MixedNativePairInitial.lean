module

public import SHE.MixedNativePairConstruction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.MixedNativeAdditiveResidualPair
open MeasureTheory PredictableL2 LowBands FiniteHaar
open scoped NNReal ENNReal
local instance nativePairInitial_finiteExponent : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance nativePairInitial_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance nativePairInitial_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)

theorem zero_input {ell M D : ℝ} (hell : 0<ell) (f : ℝ≥0×Ω→EllipticField ell M)
    (v : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : v=ᵐ[energyMeasure μ h] fun p => Real.exp (-D*(-(p.1:ℝ))) •
      NativeHeatObservation.kernel ell M hell (-(p.1:ℝ),f p)) : v=0 := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [hv,ae_eq_of_ae_eq_trim
    (Lp.coeFn_zero RealHaarIntegrand.Columns 2 ((energyMeasure μ h).trim (predictable_le_product 𝓕)))]
    with p hp hz
  have hk : NativeHeatObservation.kernel ell M hell (-(p.1:ℝ),f p)=0 :=
    NativeHeatObservation.kernel_zero hell (show -(p.1:ℝ)≤0 from neg_nonpos.mpr p.1.2) (f p)
  rw [hp,hz,hk,smul_zero]
  rfl

variable {Λ κ : ℝ} (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
variable (u₀ v₀ : StateL2) (S : Solution 𝓕 μ h Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

theorem first_zero : S.first 0=ᵐ[μ] fun _ => u₀ := by
  have hA : S.additiveInput 0=0 := zero_input 𝓕 μ h (D := 0) hκ
    (fun _ => AdditiveHaarForcing.constantField κ hκ) _ (by
      simpa only [NNReal.coe_zero,zero_sub,neg_zero,zero_mul,Real.exp_zero,one_smul]
        using S.additive_kernel 0 (by positivity))
  have hR : S.residualInput 0=0 := zero_input 𝓕 μ h (D := 0) hell _ _ (by
      simpa only [NNReal.coe_zero,zero_sub,neg_zero,zero_mul,Real.exp_zero,one_smul]
        using S.residual_kernel 0 (by positivity))
  have hIA : I₀.integral (S.additiveInput 0)=0 := by rw [hA,map_zero]
  have hIR : I₁.integral (S.residualInput 0)=0 := by rw [hR,map_zero]
  filter_upwards [S.first_mild 0 (by positivity),Lp.coeFn_zero StateL2 2 μ] with ω hω hz
  rw [hIA,hIR,hz] at hω
  simpa only [NNReal.coe_zero,NativeHeatObservation.heat,zero_div,RealHeat.realHeat_zero,
    ContinuousLinearMap.id_apply,Pi.zero_apply,add_zero] using hω

theorem second_zero : S.second 0=ᵐ[μ] fun _ => v₀ := by
  have hA : S.controlledAdditiveInput 0=0 := zero_input 𝓕 μ h hκ
    (fun _ => AdditiveHaarForcing.constantField κ hκ) _ (by
      simpa only [NNReal.coe_zero,zero_sub] using S.controlled_additive_kernel 0 (by positivity))
  have hR : S.controlledResidualInput 0=0 := zero_input 𝓕 μ h hell _ _ (by
      simpa only [NNReal.coe_zero,zero_sub] using S.controlled_residual_kernel 0 (by positivity))
  have hIA : I₀.integral (S.controlledAdditiveInput 0)=0 := by rw [hA,map_zero]
  have hIR : I₁.integral (S.controlledResidualInput 0)=0 := by rw [hR,map_zero]
  filter_upwards [S.second_mild 0 (by positivity),Lp.coeFn_zero StateL2 2 μ] with ω hω hz
  rw [hIA,hIR,hz] at hω
  simpa only [NNReal.coe_zero,NativeHeatObservation.heat,zero_div,RealHeat.realHeat_zero,
    ContinuousLinearMap.id_apply,Pi.zero_apply,add_zero,mul_zero,Real.exp_zero,one_smul,NativeClock.volterra,
    intervalIntegral.integral_same,smul_zero] using hω

end SHE.MixedNativeAdditiveResidualPair
