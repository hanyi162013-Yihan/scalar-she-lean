module

public import SHE.HilbertTrace
public import SHE.StoppedFourier

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.KernelOperator
open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {μ : Measure Ω}

/-- A square-integrable family of actual Riesz kernel rows. -/
def applyKernel (K : Lp E 2 μ) (d : E) : Lp ℂ 2 μ :=
  ((Lp.memLp K).inner_const d).toLp (fun x => inner ℂ (K x) d)

omit [CompleteSpace E] in
theorem applyKernel_ae (K : Lp E 2 μ) (d : E) :
    applyKernel K d =ᵐ[μ] fun x => inner ℂ (K x) d := MemLp.coeFn_toLp _

def linearMap (K : Lp E 2 μ) : E →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := applyKernel K
  map_add' d e := by
    apply Lp.ext
    filter_upwards [applyKernel_ae K (d+e),applyKernel_ae K d,applyKernel_ae K e,
      Lp.coeFn_add (applyKernel K d) (applyKernel K e)] with x hde hd he hsum
    rw [hde,hsum]
    simp only [Pi.add_apply,hd,he,inner_add_right]
  map_smul' c d := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [applyKernel_ae K (c • d),applyKernel_ae K d,
      Lp.coeFn_smul c (applyKernel K d)] with x hcd hd hsmul
    rw [hcd,hsmul]
    simp only [Pi.smul_apply,hd,inner_smul_right,smul_eq_mul]

omit [CompleteSpace E] in
theorem applyKernel_norm_le (K : Lp E 2 μ) (d : E) :
    ‖applyKernel K d‖ ≤ ‖K‖*‖d‖ := by
  have hh : ∀ᵐ x ∂μ, ‖applyKernel K d x‖ ≤ ‖d‖*‖K x‖ := by
    filter_upwards [applyKernel_ae K d] with x hx
    rw [hx,mul_comm]
    exact norm_inner_le_norm _ _
  simpa only [mul_comm] using Lp.norm_le_mul_norm_of_ae_le_mul hh

def operator (K : Lp E 2 μ) : E →L[ℂ] Lp ℂ 2 μ :=
  (linearMap K).mkContinuous ‖K‖ (applyKernel_norm_le K)

omit [CompleteSpace E] in
theorem operator_column_sq (K : Lp E 2 μ) (d : E) :
    ‖operator K d‖^2 = ∫ x, ‖inner ℂ (K x) d‖^2 ∂μ := by
  change ‖applyKernel K d‖^2 = _
  exact StoppedFourier.toLp_norm_sq_eq_integral ((Lp.memLp K).inner_const d)

/-- The actual integral-kernel operator has finite basis trace bounded
by its spatial L² mass. Finite Bessel sums justify every exchange, so
the bound does not assume a Hilbert--Schmidt identity. -/
theorem operator_trace (K : Lp E 2 μ) (b : HilbertBasis I ℂ E) :
    Summable (fun i => ‖operator K (b i)‖^2) ∧
      (∑' i, ‖operator K (b i)‖^2) ≤ ‖K‖^2 := by
  have hi (i : I) : Integrable (fun x => ‖inner ℂ (K x) (b i)‖^2) μ :=
    ((Lp.memLp K).inner_const (b i)).integrable_norm_pow (by norm_num)
  have hfinite (s : Finset I) : (∑ i ∈ s, ‖operator K (b i)‖^2) ≤ ‖K‖^2 := by
    simp_rw [operator_column_sq]
    rw [← integral_finsetSum s (fun i _ => hi i),StoppedFourier.L2_norm_sq_eq_integral]
    apply integral_mono (integrable_finsetSum s (fun i _ => hi i))
      ((Lp.memLp K).integrable_norm_pow (by norm_num))
    intro x
    have hp := HilbertTrace.basis_sq b (K x)
    calc
      _ = ∑ i ∈ s, ‖inner ℂ (b i) (K x)‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi'
        rw [norm_inner_symm]
      _ ≤ ∑' i, ‖inner ℂ (b i) (K x)‖^2 :=
        hp.1.sum_le_tsum s (fun _ _ => sq_nonneg _)
      _ = _ := hp.2
  exact ⟨summable_of_sum_le (fun i => sq_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun i => sq_nonneg _) hfinite⟩

/-- An arbitrarily dependent bounded right factor can be retained
without an independence assumption or a rough negative-norm multiplier. -/
theorem operator_right_trace {G J Kidx : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (K : Lp E 2 μ) (R : G →L[ℂ] E)
    (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ (Lp ℂ 2 μ))
    (g : HilbertBasis Kidx ℂ G) :
    Summable (fun k => ‖((operator K).comp R) (g k)‖^2) ∧
      (∑' k, ‖((operator K).comp R) (g k)‖^2) ≤ ‖R‖^2*‖K‖^2 := by
  have ht := operator_trace K b
  have hh := HilbertTrace.right_comp (operator K) R b c g ht.1
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg _))⟩

/-- A random kernel and its random right noise factor need not be
independent. Their actual trace is controlled by the true kernel mass
and a pathwise operator bound; integrability is a conclusion. -/
theorem expected_right_trace_bound
    {W G J Kidx : Type*} [MeasurableSpace W] (P : Measure W)
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (K : W → Lp E 2 μ) (R : W → G →L[ℂ] E)
    (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ (Lp ℂ 2 μ))
    (g : HilbertBasis Kidx ℂ G) {C A : ℝ} (hC : 0 ≤ C)
    (hR : ∀ ω, ‖R ω‖^2 ≤ C)
    (hK : Integrable (fun ω => ‖K ω‖^2) P)
    (hKA : (∫ ω, ‖K ω‖^2 ∂P) ≤ A)
    (hm : AEStronglyMeasurable
      (fun ω => ∑' k, ‖((operator (K ω)).comp (R ω)) (g k)‖^2) P) :
    Integrable (fun ω => ∑' k, ‖((operator (K ω)).comp (R ω)) (g k)‖^2) P ∧
      (∫ ω, ∑' k, ‖((operator (K ω)).comp (R ω)) (g k)‖^2 ∂P) ≤ C*A := by
  have hb (ω : W) : (∑' k, ‖((operator (K ω)).comp (R ω)) (g k)‖^2) ≤ C*‖K ω‖^2 :=
    (operator_right_trace (K ω) (R ω) b c g).2.trans
      (mul_le_mul_of_nonneg_right (hR ω) (sq_nonneg _))
  have hi : Integrable (fun ω => ∑' k, ‖((operator (K ω)).comp (R ω)) (g k)‖^2) P := by
    apply (hK.const_mul C).mono' hm
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
    exact hb ω
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, C*‖K ω‖^2 ∂P := integral_mono hi (hK.const_mul C) hb
    _ = C*∫ ω, ‖K ω‖^2 ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hKA hC

end SHE.KernelOperator
