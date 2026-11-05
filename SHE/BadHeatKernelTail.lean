module

public import SHE.NormalizedHeatMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NormalizedKernelSplit
open MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel
open scoped ENNReal
local instance badHeatKernelTail_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance badHeatKernelTail_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance badHeatKernelTail_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance badHeatKernelTail_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

/-- The actual manuscript bad branch: normalization by
D δ^(-1/2) w^(1/4) p_(8w), truncation before the true right heat, and a
high fixed moment yield an arbitrary polynomial λ-tail. The w-density
has canceled through the proved native heat-square mass. -/
theorem expected_bad_heat_trace_polynomial
    {Ω G N : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [Countable N]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Ω × Space → ℝ} (hA : Measurable A)
    {D δ w B C Cnoise Λ ρ lam ε P : ℝ}
    (hδ : 0 < δ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hB : 0 ≤ B) (hb : ∀ ω y x, ‖fullKernel (heatEnvelope D δ w) A (ω,(y,x))‖ ≤ B)
    (hC : 0 ≤ C) (m : ℕ) (hlam : 1 ≤ lam) (hExponent : P ≤ ε*(2*m))
    (hAn : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      Integrable (fun ω => |A (ω,p)|^(2*m+2)) μ)
    (hbound : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      (∫ ω, |A (ω,p)|^(2*m+2) ∂μ) ≤ C)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (S : Ω → G →L[ℂ] CircleL2) (g : HilbertBasis N ℂ G)
    (hCnoise : 0 ≤ Cnoise) (hS : ∀ ω, ‖S ω‖^2 ≤ Cnoise)
    (hSmeas : ∀ n, Measurable (fun ω => S ω (g n))) :
    Integrable (fun ω => ∑' n, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ
      (integralOperator (badKernel (heatEnvelope D δ w) A (lam^ε)) ω
        (circleHeatOperator (δ/2) (by positivity) (S ω (g n))))‖^2) μ ∧
      (∫ ω, ∑' n, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ
        (integralOperator (badKernel (heatEnvelope D δ w) A (lam^ε)) ω
          (circleHeatOperator (δ/2) (by positivity) (S ω (g n))))‖^2 ∂μ) ≤
        Cnoise*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-P) := by
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have h := expected_bad_right_trace μ (heatEnvelope_continuous hw).measurable hA hB hb
    (Real.rpow_pos_of_pos hlam0 ε) hC m (heatEnvelope_sq_integrable hw) hAn hbound
    hΛ hρ hδ S g hCnoise hS hSmeas
  have htail : C/(lam^ε)^(2*m) ≤ C*lam^(-P) := by
    calc
      _ = C*lam^(-(ε*(2*m))) := by
        rw [← Real.rpow_mul_natCast hlam0.le,div_eq_mul_inv,← Real.rpow_neg hlam0.le]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlam (by linarith)) hC
  have hmass := heatEnvelope_sq_mass (D:=D) hδ hw hw1
  have hI : 0 ≤ ∫ p : Space, heatEnvelope D δ w p^2 ∂(haarAddCircle (T:=2*π)).prod haarAddCircle :=
    integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨h.1,h.2.trans ?_⟩
  calc
    _ ≤ Cnoise*((C*lam^(-P))*∫ p : Space, heatEnvelope D δ w p^2 ∂(haarAddCircle (T:=2*π)).prod haarAddCircle) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htail hI) hCnoise
    _ ≤ Cnoise*((C*lam^(-P))*(heatMassConstant*D^2*δ^(-1:ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (mul_nonneg hC (Real.rpow_nonneg hlam0.le _))) hCnoise
    _ = _ := by ring

end SHE.NormalizedKernelSplit
