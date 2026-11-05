module

public import SHEStochastic.MatrixHaarKernel
public import SHEStochastic.CausalKernelInput
public import SHE.HaarIntegrandEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixFixedHaarInput
open MeasureTheory SHE SHE.FiniteHaar SHE.PredictableL2 MatrixInfiniteHaar MatrixHaarKernel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Columns (d := d)) := borel _
local instance : BorelSpace (Columns (d := d)) := ⟨rfl⟩

def constant (d : Type*) [Fintype d] (U : ℝ) := (Fintype.card d : ℝ) * HaarIntegrandEnergy.singleConstant U

theorem constant_nonneg {U : ℝ} (hU : 0 ≤ U) : 0 ≤ constant d U :=
  mul_nonneg (Nat.cast_nonneg _) (HaarIntegrandEnergy.singleConstant_nonneg hU)

theorem constant_mono {U V : ℝ} (hUV : U ≤ V) : constant d U ≤ constant d V := by
  have hG := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ) < 1/2)).le
  unfold constant HaarIntegrandEnergy.singleConstant
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUV (by positivity)) (Nat.cast_nonneg _)

theorem kernel_zero {τ : ℝ} (hτ : τ ≤ 0) (P : Profile d) : kernel τ P = 0 := by
  rw [kernel, dif_neg (not_lt.mpr hτ)]

theorem small_bound {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (P : Profile d) :
    ‖kernel τ P‖ ^ 2 ≤ constant d P.upper * τ ^ (-(1/2 : ℝ)) := by
  have hs : 1 ≤ τ ^ (-(1/2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
  apply (MatrixHaarKernel.norm_sq hτ P).trans
  unfold constant HaarIntegrandEnergy.singleConstant
  have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (Nat.cast_nonneg (Fintype.card d)) P.upper_pos.le)
  nlinarith only [hh]

def horizonConstant (d : Type*) [Fintype d] (H : ℝ≥0) (U : ℝ) : ℝ :=
  constant d U * (max 1 (H : ℝ)) ^ (1/2 : ℝ)

theorem horizonConstant_nonneg (H : ℝ≥0) {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ horizonConstant d H U :=
  mul_nonneg (constant_nonneg hU) (Real.rpow_nonneg (le_max_of_le_left zero_le_one) _)

theorem horizonConstant_mono (H : ℝ≥0) {U V : ℝ} (hUV : U ≤ V) :
    horizonConstant d H U ≤ horizonConstant d H V :=
  mul_le_mul_of_nonneg_right (constant_mono hUV)
    (Real.rpow_nonneg (le_max_of_le_left zero_le_one) _)

/-- The same actual HS kernel has the integrable heat bound on every
finite horizon. Only its deterministic constant changes with the horizon. -/
theorem horizon_bound (H : ℝ≥0) {τ : ℝ} (hτ : 0 < τ) (hτH : τ ≤ H) (P : Profile d) :
    ‖kernel τ P‖ ^ 2 ≤ horizonConstant d H P.upper * τ ^ (-(1/2 : ℝ)) := by
  let R : ℝ := max 1 (H : ℝ)
  have hR : 1 ≤ R := le_max_left _ _
  have hτR : τ ≤ R := hτH.trans (le_max_right _ _)
  have hhalf : 1 ≤ R ^ (1/2 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hone : 1 ≤ R ^ (1/2 : ℝ) * τ ^ (-(1/2 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hτ.le hτR (by norm_num : 0 ≤ (1/2 : ℝ)))
      (Real.rpow_nonneg hτ.le (-(1/2 : ℝ)))
    rw [← Real.rpow_add hτ, add_neg_cancel, Real.rpow_zero] at hh
    exact hh
  have hG : 0 ≤ 2 * HeatTrace.fractionalGaussianIntegral 0 :=
    mul_nonneg (by norm_num) (HeatTrace.fractionalGaussianIntegral_pos (by norm_num)).le
  have hmore := mul_le_mul_of_nonneg_right hhalf
    (mul_nonneg hG (Real.rpow_nonneg hτ.le (-(1/2 : ℝ))))
  have hn := mul_le_mul_of_nonneg_left (add_le_add hone hmore)
    (mul_nonneg (Nat.cast_nonneg (Fintype.card d)) P.upper_pos.le)
  apply (MatrixHaarKernel.norm_sq hτ P).trans
  unfold horizonConstant constant HaarIntegrandEnergy.singleConstant
  dsimp only [R] at hn
  nlinarith only [hn]

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d)
  (hUpper : ∀ p, (Q p).upper ≤ U)
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

include hH hU hUpper in
theorem energy (t : ℝ≥0) (ht : t ≤ H) :
    (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖kernel ((t : ℝ)-(s : ℝ)) (Q (s,ω))‖ ^ 2) ∂μ ∂timeMeasure H) ≤
      ENNReal.ofReal (constant d U * (2 * (t : ℝ) ^ (1/2 : ℝ))) := by
  apply CausalKernelInput.fixed_energy (fun τ p => kernel τ (Q p))
    (fun τ hτ p => kernel_zero hτ (Q p)) (constant d U) (constant_nonneg hU) _ μ hH ht
  intro τ hτ hτ1 p
  exact (small_bound hτ hτ1 (Q p)).trans
    (mul_le_mul_of_nonneg_right (constant_mono (hUpper p)) (Real.rpow_nonneg hτ.le _))

include hU hUpper in
theorem horizon_energy (t : ℝ≥0) (ht : t ≤ H) :
    (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖kernel ((t : ℝ)-(s : ℝ)) (Q (s,ω))‖ ^ 2) ∂μ ∂timeMeasure H) ≤
      ENNReal.ofReal (horizonConstant d H U * (2 * (t : ℝ) ^ (1/2 : ℝ))) := by
  apply CausalKernelInput.fixed_energy_upto (H : ℝ) (fun τ p => kernel τ (Q p))
    (fun τ hτ p => kernel_zero hτ (Q p)) (horizonConstant d H U)
    (horizonConstant_nonneg H hU) _ μ le_rfl ht
  intro τ hτ hτH p
  exact (horizon_bound H hτ hτH (Q p)).trans
    (mul_le_mul_of_nonneg_right (horizonConstant_mono H (hUpper p)) (Real.rpow_nonneg hτ.le _))

include hU hUpper hQ in
theorem memLp (t : ℝ≥0) (ht : t ≤ H) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0 × Ω => kernel ((t : ℝ)-(p.1 : ℝ)) (Q p)) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  apply CausalKernelInput.memLp_upto (H : ℝ) F μ H le_rfl (fun τ p => kernel τ (Q p))
    (fun τ hτ p => kernel_zero hτ (Q p)) (horizonConstant d H U)
    (horizonConstant_nonneg H hU) _ t ht
    (MatrixHaarKernel.predictable F Q hQ t)
  intro τ hτ hτH p
  exact (horizon_bound H hτ hτH (Q p)).trans
    (mul_le_mul_of_nonneg_right (horizonConstant_mono H (hUpper p)) (Real.rpow_nonneg hτ.le _))

def input (t : ℝ≥0) (ht : t ≤ H) : Process (E := Columns (d := d)) F μ H :=
  (memLp F μ H U hU Q hUpper hQ t ht).toLp (fun p => kernel ((t : ℝ)-(p.1 : ℝ)) (Q p))

theorem input_ae (t : ℝ≥0) (ht : t ≤ H) :
    input F μ H U hU Q hUpper hQ t ht =ᵐ[energyMeasure μ H]
      (fun p : ℝ≥0 × Ω => kernel ((t : ℝ)-(p.1 : ℝ)) (Q p)) :=
  ae_eq_of_ae_eq_trim (memLp F μ H U hU Q hUpper hQ t ht).coeFn_toLp

theorem input_stopped (t : ℝ≥0) (ht : t ≤ H) :
    ∀ᵐ p ∂energyMeasure μ H, t < p.1 → input F μ H U hU Q hUpper hQ t ht p = 0 := by
  filter_upwards [input_ae F μ H U hU Q hUpper hQ t ht] with p hp hpt
  rw [hp, kernel_zero (sub_nonpos.mpr (by exact_mod_cast hpt.le))]

end SHEStochastic.MatrixFixedHaarInput
