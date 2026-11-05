module

public import SHE.NativeKernelConversion
public import SHE.NativeKernelMass
public import SHE.KernelOutputTrace
public import SHE.PositiveKernels

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NormalizedKernelSplit
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier NativeRandomKernel
open scoped ENNReal
local instance normalizedKernelSplit_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance normalizedKernelSplit_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance normalizedKernelSplit_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance normalizedKernelSplit_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance normalizedKernelSplit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance normalizedKernelSplit_kernelSecondCountable : SecondCountableTopology KernelSpace := Lp.SecondCountableTopology
local instance normalizedKernelSplit_kernelMeasurable : MeasurableSpace KernelSpace := borel KernelSpace
local instance normalizedKernelSplit_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩

abbrev Space := HeatCircle × HeatCircle
variable {Ω : Type*} [MeasurableSpace Ω]

def fullKernel (H : Space → ℝ) (A : Ω × Space → ℝ) (p : Ω × Space) : ℂ :=
  (H p.2*A p : ℝ)

def badKernel (H : Space → ℝ) (A : Ω × Space → ℝ) (R : ℝ) (p : Ω × Space) : ℂ :=
  (H p.2*badAmplitude R (A p) : ℝ)

def goodKernel (H : Space → ℝ) (A : Ω × Space → ℝ) (R : ℝ) (p : Ω × Space) : ℂ :=
  fullKernel H A p-badKernel H A R p

theorem fullKernel_measurable {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) : Measurable (fullKernel H A) :=
  Complex.continuous_ofReal.measurable.comp ((hH.comp measurable_snd).mul hA)

theorem badKernel_measurable {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) (R : ℝ) : Measurable (badKernel H A R) :=
  Complex.continuous_ofReal.measurable.comp ((hH.comp measurable_snd).mul (badAmplitude_measurable hA R))

theorem goodKernel_measurable {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) (R : ℝ) : Measurable (goodKernel H A R) :=
  (fullKernel_measurable hH hA).sub (badKernel_measurable hH hA R)

theorem badKernel_bound {H : Space → ℝ} {A : Ω × Space → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B) (R : ℝ) (ω : Ω) (y x : HeatCircle) :
    ‖badKernel H A R (ω,(y,x))‖ ≤ B := by
  by_cases hh : R < |A (ω,(y,x))|
  · simpa only [badKernel,badAmplitude,ite_eq_left hh,fullKernel] using hb ω y x
  · simpa only [badKernel,badAmplitude,ite_eq_right hh,mul_zero,Complex.ofReal_zero,norm_zero] using hB

theorem goodKernel_bound {H : Space → ℝ} {A : Ω × Space → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B) (R : ℝ) (ω : Ω) (y x : HeatCircle) :
    ‖goodKernel H A R (ω,(y,x))‖ ≤ B := by
  by_cases hh : R < |A (ω,(y,x))|
  · simpa only [goodKernel,fullKernel,badKernel,badAmplitude,ite_eq_left hh,sub_self,norm_zero] using hB
  · simpa only [goodKernel,fullKernel,badKernel,badAmplitude,ite_eq_right hh,mul_zero,Complex.ofReal_zero,sub_zero]
      using hb ω y x

/-- The normalized amplitude is truncated before applying either right
factor. This is a genuine pathwise kernel envelope. -/
theorem goodKernel_envelope {H : Space → ℝ} {A : Ω × Space → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (p : Ω × Space) : ‖goodKernel H A R p‖ ≤ R*|H p.2| := by
  by_cases hh : R < |A p|
  · simp only [goodKernel,fullKernel,badKernel,badAmplitude,ite_eq_left hh,sub_self,norm_zero]
    exact mul_nonneg hR (abs_nonneg _)
  · simp only [goodKernel,fullKernel,badKernel,badAmplitude,ite_eq_right hh,mul_zero,Complex.ofReal_zero,
      sub_zero,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (le_of_not_gt hh) (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- High normalized-amplitude moments control the actual bad kernel
mass. The coarse bound supplies only true L²/Fubini applicability. -/
theorem expected_bad_kernel_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    {H : Space → ℝ} {A : Ω × Space → ℝ} (hH : Measurable H) (hA : Measurable A)
    {B R C : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B)
    (hR : 0 < R) (hC : 0 ≤ C) (m : ℕ)
    (hH2 : Integrable (fun p => H p^2) ((haarAddCircle (T:=2*π)).prod haarAddCircle))
    (hAn : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      Integrable (fun ω => |A (ω,p)|^(2*m+2)) μ)
    (hbound : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      (∫ ω, |A (ω,p)|^(2*m+2) ∂μ) ≤ C) :
    Integrable (fun ω => ‖kernel (badKernel H A R) ω‖^2) μ ∧
      (∫ ω, ‖kernel (badKernel H A R) ω‖^2 ∂μ) ≤
        C/R^(2*m)*∫ p : Space, H p^2 ∂(haarAddCircle (T:=2*π)).prod haarAddCircle := by
  have hm := badKernel_measurable hH hA R
  have hbb := badKernel_bound hB hb R
  refine ⟨kernel_mass_integrable μ hm hB hbb,?_⟩
  have h := weighted_bad_kernel_bound μ ((haarAddCircle (T:=2*π)).prod haarAddCircle)
    A H m C hR hC hA hH hH2 hAn hbound
  simpa only [kernel_norm_sq hm hB hbb,badKernel,Complex.norm_real,Real.norm_eq_abs,sq_abs] using h

/-- The bad branch keeps its true right heat S_(δ/2), discards the
negative-output gain only through Q≤I, and allows arbitrary dependence
between the amplitude and the bounded right noise factor. -/
theorem expected_bad_right_trace
    {G N : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [Countable N]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {H : Space → ℝ} {A : Ω × Space → ℝ} (hH : Measurable H) (hA : Measurable A)
    {B R C Cnoise Λ ρ δ : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B)
    (hR : 0 < R) (hC : 0 ≤ C) (m : ℕ)
    (hH2 : Integrable (fun p => H p^2) ((haarAddCircle (T:=2*π)).prod haarAddCircle))
    (hAn : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      Integrable (fun ω => |A (ω,p)|^(2*m+2)) μ)
    (hbound : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      (∫ ω, |A (ω,p)|^(2*m+2) ∂μ) ≤ C)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (S : Ω → G →L[ℂ] CircleL2) (g : HilbertBasis N ℂ G)
    (hCnoise : 0 ≤ Cnoise) (hS : ∀ ω, ‖S ω‖^2 ≤ Cnoise)
    (hSmeas : ∀ n, Measurable (fun ω => S ω (g n))) :
    Integrable (fun ω => ∑' n, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ
      (integralOperator (badKernel H A R) ω
        (circleHeatOperator (δ/2) (by positivity) (S ω (g n))))‖^2) μ ∧
      (∫ ω, ∑' n, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ
        (integralOperator (badKernel H A R) ω
          (circleHeatOperator (δ/2) (by positivity) (S ω (g n))))‖^2 ∂μ) ≤
        Cnoise*(C/R^(2*m)*∫ p : Space, H p^2 ∂(haarAddCircle (T:=2*π)).prod haarAddCircle) := by
  have hk := expected_bad_kernel_mass μ hH hA hB hb hR hC m hH2 hAn hbound
  have hm := kernel_measurable (badKernel_measurable hH hA R) hB (badKernel_bound hB hb R)
  let S' : Ω → G →L[ℂ] CircleL2 := fun ω => (circleHeatOperator (δ/2) (by positivity)).comp (S ω)
  have hheat : ‖circleHeatOperator (δ/2) (by positivity)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ)≤1)
    intro z
    simpa only [one_mul] using circleHeatOperator_norm_le (δ/2) (by positivity) z
  have hs' (ω : Ω) : ‖S' ω‖^2 ≤ Cnoise := by
    have hh : ‖S' ω‖ ≤ ‖S ω‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_right hheat (norm_nonneg _)).trans_eq (one_mul _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans (hS ω)
  have hsm (n : N) : Measurable (fun ω => S' ω (g n)) :=
    (circleHeatOperator (δ/2) (by positivity)).continuous.measurable.comp (hSmeas n)
  have h := KernelOperator.expected_output_right_trace_bound μ
    (kernel (badKernel H A R)) hm (OneInputOperator.besselHalf Λ ρ hΛ hρ)
    (OneInputOperator.besselHalf_opNorm_le Λ ρ hΛ hρ) S' g
    (fourierBasis (T:=2*π)) (fourierBasis (T:=2*π)) hsm hCnoise hs' hk.1 hk.2
  simpa only [ContinuousLinearMap.comp_apply,integralOperator,S'] using h

end SHE.NormalizedKernelSplit
