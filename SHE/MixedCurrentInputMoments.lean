module

public import SHE.HeatEnergyFatou

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedHeatedDifferenceMoments
open Set Filter MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedCurrentInputMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
local instance mixedCurrentInputMoments_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedCurrentInputMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCurrentInputMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCurrentInputMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCurrentInputMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCurrentInputMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCurrentInputMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

theorem momentConstant_nonneg (hκ0 : 0≤κ) (hM : 0≤M) (n : ℕ) (B : ℝ≥0) : 0≤momentConstant n B κ M := by
  have hU := ProfileVariance.upperConstant_pos
  unfold momentConstant NativeHybridMoments.momentConstant
  positivity

theorem difference_measurable (q : ℝ≥0) : Measurable (fun ω=>S.second q ω-S.first q ω) := by
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  exact hV.sub hU

include hIJ₀ hIJ₁ in
theorem fractional_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {τ : ℝ} (hτ : 0<τ) (x : HeatCircle) (n : ℕ) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower n J B) {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω=>|functional τ x (S.second q ω-S.first q ω)|^(((2*n:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|functional τ x (S.second q ω-S.first q ω)|^(((2*n:ℕ):ℝ)*β) ∂μ)≤
        momentConstant n B κ M^β := by
  let D : Ω→ℝ := fun ω=>functional τ x (S.second q ω-S.first q ω)
  have hm : Measurable D := (functional τ x).continuous.measurable.comp
    (difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q)
  have hh := even_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 hτ x n B hBDG
  have hC := momentConstant_nonneg (κ:=κ) hκ.le (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) n B
  have hb : (∫⁻ ω,ENNReal.ofReal (‖D ω‖^(((2*n:ℕ):ℝ))) ∂μ)≤ENNReal.ofReal (momentConstant n B κ M) := by
    simp only [Real.rpow_natCast,Real.norm_eq_abs]
    rw [←ofReal_integral_eq_lintegral_ofReal hh.1 (ae_of_all _ (fun ω=>pow_nonneg (abs_nonneg _) _))]
    exact ENNReal.ofReal_le_ofReal hh.2
  have hf := FractionalMoment.moment_fraction hm.aestronglyMeasurable hβ hβ1 hC hb
  exact RealMomentBound.integral_bound μ _
    (hm.norm.aemeasurable.pow_const _).aestronglyMeasurable
    (fun ω=>rpow_nonneg (abs_nonneg (D ω)) _) (rpow_nonneg hC _) (by
      simpa only [Real.norm_eq_abs] using hf)

include hIJ₀ hIJ₁ in
/-- The literal current difference has finite global second energy.
The proof uses only positive-age native observations and Fatou; it
does not assume a current-state L² moment as extra stochastic input. -/
theorem current_energy (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (n : ℕ) (hn : 0<n) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower n J B) :
    Integrable (fun ω=>‖S.second q ω-S.first q ω‖^2) μ ∧
      (∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)≤momentConstant n B κ M^(1/(n:ℝ)) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hβ0 : 0≤1/(n:ℝ) := by positivity
  have hβ1 : 1/(n:ℝ)≤1 := (div_le_one hnR).mpr (by exact_mod_cast hn)
  have hC := momentConstant_nonneg (κ:=κ) hκ.le (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) n B
  apply HeatedCurrentInput.energy_of_heated_moments μ (fun ω=>S.second q ω-S.first q ω)
    (difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q)
    (rpow_nonneg hC _)
  intro τ hτ x
  have hh := fractional_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 hτ x n B hBDG hβ0 hβ1
  have he : (((2*n:ℕ):ℝ))*(1/(n:ℝ))=2 := by push_cast;field_simp
  simpa only [he,Real.rpow_two,sq_abs,HeatedCurrentInput.field] using hh

end SHE.MixedHeatedDifferenceMoments
