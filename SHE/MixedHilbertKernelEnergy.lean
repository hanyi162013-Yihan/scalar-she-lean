module

public import SHE.SeparatedHilbertKernel
public import SHE.MixedHilbertInputMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.MixedHilbertKernelEnergy
open Set Filter MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
  NativeRandomKernel
open scoped NNReal ENNReal
local instance mixedHilbertKernelEnergy_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
local instance mixedHilbertKernelEnergy_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedHilbertKernelEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedHilbertKernelEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedHilbertKernelEnergy_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance mixedHilbertKernelEnergy_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedHilbertKernelEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedHilbertKernelEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedHilbertKernelEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedHilbertKernelEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
/-- The actual globally constructed mixed current difference can be
tested against a kernel depending arbitrarily on its entire random
past. Every input moment is derived from the original common-driver
solution; only the kernel's true relative moment and literal right-heat
factorization remain to be supplied by the physical Gaussian word. -/
theorem actual_input_energy (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (k p : ℕ) (hp : 0<p) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (F G : Ω×(HeatCircle×HeatCircle)→ℂ) (hG : Measurable G)
    {B : ℝ} (hB : 0≤B) (hbound : ∀ ω y x,‖G (ω,(y,x))‖≤B)
    (τ : ℝ) (hτ : 0≤τ)
    {mass ρ w A χ CG : ℝ} (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (hw : 0<w) (hw1 : w≤1) (hA : 0≤A) (hχ0 : 0≤χ) (hχ1 : χ<1)
    (hCG : 0≤CG) (horder : 1≤(p:ℝ)*(1-χ))
    (hMom : ∀ᵐ z : HeatCircle×HeatCircle ∂(AddCircle.haarAddCircle (T:=2*π)).prod AddCircle.haarAddCircle,
      (∫ ω,‖G (ω,z)‖^(4*p) ∂μ)≤CG*(A*‖ProfileVariance.heatPhysical (8*w) z.1 z.2‖)^(4*p))
    (hsplit : ∀ ω,integralOperator F ω (embed (S.second q ω-S.first q ω))=
      integralOperator G ω (HeatedCurrentInput.value τ (fun ω=>S.second q ω-S.first q ω) ω)) :
    let CD := MixedHeatedDifferenceMoments.momentConstant ((2*p)*(k+2)) B0 κ M^((1-χ)/(k+2:ℝ))
    let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*A^2*((CD+CG)/2)^(1/(p:ℝ))
    Integrable (fun ω=>‖OneInputOperator.besselHalf mass ρ hmass hρ.le
      (integralOperator F ω (embed (S.second q ω-S.first q ω)))‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (integralOperator F ω (embed (S.second q ω-S.first q ω)))‖^2 ∂μ)≤
        C*(∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)^χ := by
  intro CD C
  have hn : 0<p*(k+2) := Nat.mul_pos hp (by omega)
  have hN : 0<(2*p)*(k+2) := Nat.mul_pos (Nat.mul_pos (by norm_num) hp) (by omega)
  have hβ0 : 0≤(1-χ)/(k+2:ℝ) := div_nonneg (sub_pos.mpr hχ1).le (by positivity)
  have hβ1 : (1-χ)/(k+2:ℝ)≤1 := (div_le_one (by positivity : (0:ℝ)<k+2)).mpr (by linarith)
  have hm := MixedHeatedDifferenceMoments.difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q
  have hi := MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hq1 ((2*p)*(k+2)) hN B0 hBDG
  have hh := MixedHeatedDifferenceMoments.current_fractional_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ q hqH hq1 (p*(k+2)) hn B0
    (by simpa only [Nat.mul_assoc] using hBDG) hβ0 hβ1
  have he : (((4*(p*(k+2)):ℕ):ℝ))*((1-χ)/(k+2:ℝ))=4*(p:ℝ)*(1-χ) := by
    push_cast
    field_simp
    <;> ring
  simp only [←Nat.mul_assoc] at hh he
  rw [he] at hh
  have hCD : 0≤CD := rpow_nonneg (MixedHeatedDifferenceMoments.momentConstant_nonneg (κ:=κ) hκ.le
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) ((2*p)*(k+2)) B0) _
  exact separated_hilbert_energy (Ω:=Ω) μ F G hG hB hbound τ hτ
    (fun ω : Ω=>S.second q ω-S.first q ω) hm hi.1 hmass hρ hρhalf hw hw1 hA hχ0 hχ1 hCD hCG
    p hp horder hh.1 hh.2 hMom hsplit

end SHE.MixedHilbertKernelEnergy
