module

public import SHE.HeatedHilbertMoments
public import SHE.MixedCurrentInputMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedHeatedDifferenceMoments
open Set Filter MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedHilbertInputMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
local instance mixedHilbertInputMoments_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedHilbertInputMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedHilbertInputMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedHilbertInputMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedHilbertInputMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedHilbertInputMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedHilbertInputMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

include hIJ₀ hIJ₁ in
/-- Actual all-order global Hilbert moments of the common-driver
mixed current difference. The kernel against which this state is later
tested may depend on its entire past and on every current noise. -/
theorem current_four_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (n : ℕ) (hn : 0<n) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower (2*n) J B) :
    Integrable (fun ω=>‖S.second q ω-S.first q ω‖^(4*n)) μ ∧
      (∫ ω,‖S.second q ω-S.first q ω‖^(4*n) ∂μ)≤momentConstant (2*n) B κ M := by
  apply HeatedCurrentInput.four_moment_of_heated_moments μ
    (fun ω=>S.second q ω-S.first q ω)
    (difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q) n hn
    (momentConstant_nonneg (κ:=κ) hκ.le (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) (2*n) B)
  intro τ hτ x
  have hh := even_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 hτ x (2*n) B hBDG
  have he (z : ℝ) : |z|^(2*(2*n))=z^(4*n) := by
    rw [pow_abs_two_mul]
    congr 1
    omega
  simpa only [he,HeatedCurrentInput.field] using hh

include hIJ₀ hIJ₁ in
theorem current_fractional_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (n : ℕ) (hn : 0<n) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower (2*n) J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω=>‖S.second q ω-S.first q ω‖^(((4*n:ℕ):ℝ)*β)) μ ∧
      (∫ ω,‖S.second q ω-S.first q ω‖^(((4*n:ℕ):ℝ)*β) ∂μ)≤momentConstant (2*n) B κ M^β := by
  let D : Ω→ℝ := fun ω=>‖S.second q ω-S.first q ω‖
  have hm : Measurable D :=
    (difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q).norm
  have hh := current_four_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 n hn B hBDG
  have hC := momentConstant_nonneg (κ:=κ) hκ.le (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) (2*n) B
  have hb : (∫⁻ ω,ENNReal.ofReal (‖D ω‖^(((4*n:ℕ):ℝ))) ∂μ)≤ENNReal.ofReal (momentConstant (2*n) B κ M) := by
    simp only [Real.rpow_natCast,D,Real.norm_of_nonneg (norm_nonneg _)]
    rw [←ofReal_integral_eq_lintegral_ofReal hh.1 (ae_of_all _ (fun ω=>pow_nonneg (norm_nonneg _) _))]
    exact ENNReal.ofReal_le_ofReal hh.2
  have hf := FractionalMoment.moment_fraction hm.aestronglyMeasurable hβ hβ1 hC hb
  simp only [D,Real.norm_of_nonneg (norm_nonneg _)] at hf
  exact RealMomentBound.integral_bound μ _
    (hm.pow_const _).aestronglyMeasurable (fun ω=>rpow_nonneg (norm_nonneg _) _)
    (rpow_nonneg hC _) hf

end SHE.MixedHeatedDifferenceMoments
