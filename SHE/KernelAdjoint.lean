module

public import SHE.KernelOperator
public import SHE.MeasurableL2Field

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.KernelOperator
open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {X E I J : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ν : Measure X}

theorem operator_norm_le (K : Lp E 2 ν) : ‖operator K‖ ≤ ‖K‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (applyKernel_norm_le K)

theorem operator_sub (K L : Lp E 2 ν) : operator (K-L)=operator K-operator L := by
  apply ContinuousLinearMap.ext
  intro d
  apply Lp.ext
  filter_upwards [applyKernel_ae (K-L) d,applyKernel_ae K d,applyKernel_ae L d,
    Lp.coeFn_sub K L,Lp.coeFn_sub (operator K d) (operator L d)] with x hkl hk hl he hsub
  change applyKernel (K-L) d x = (operator K-operator L) d x
  change applyKernel (K-L) d x = (operator K d-operator L d) x
  rw [hkl,hsub,Pi.sub_apply,he,Pi.sub_apply,inner_sub_left]
  exact congrArg₂ (·-·) hk.symm hl.symm

theorem operator_lipschitz : LipschitzWith 1 (operator (μ:=ν) (E:=E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro K L
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul,← operator_sub] using operator_norm_le (K-L)

theorem operator_continuous : Continuous (operator (μ:=ν) (E:=E)) :=
  operator_lipschitz.continuous

/-- The synthesis operator of an actual square-integrable vector kernel.
It is the adjoint of its Riesz analysis map. -/
def synthesis (K : Lp E 2 ν) : Lp ℂ 2 ν →L[ℂ] E := (operator K).adjoint

theorem integrable_smul_kernel (K : Lp E 2 ν) (v : Lp ℂ 2 ν) :
    Integrable (fun x => v x • K x) ν := by
  apply ((Lp.memLp v).norm.integrable_mul (Lp.memLp K).norm).mono'
    ((Lp.memLp v).aestronglyMeasurable.smul (Lp.memLp K).aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    change ‖v x • K x‖ ≤ ‖v x‖*‖K x‖
    rw [norm_smul])

/-- This adjoint is literally the Bochner integral against the vector
kernel, rather than an independently postulated Hilbert--Schmidt map. -/
theorem synthesis_eq_integral (K : Lp E 2 ν) (v : Lp ℂ 2 ν) :
    synthesis K v = ∫ x, v x • K x ∂ν := by
  have hi := integrable_smul_kernel K v
  apply ext_inner_left ℂ
  intro d
  rw [synthesis,ContinuousLinearMap.adjoint_inner_right,L2.inner_def,← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [applyKernel_ae K d] with x hx
  change inner ℂ (applyKernel K d x) (v x)=inner ℂ d (v x • K x)
  rw [hx,inner_smul_right,RCLike.inner_apply]
  rw [← inner_conj_symm]
  simp only [starRingEnd_self_apply]

/-- Bounded output operators act on the true integral kernel and on its
synthesis operator in exactly the same way. -/
theorem synthesis_compLp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (Q : E →L[ℂ] F) (K : Lp E 2 ν) :
    synthesis (Q.compLp K)=Q.comp (synthesis K) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [synthesis_eq_integral]
  change _=Q (synthesis K v)
  rw [synthesis_eq_integral,← Q.integral_comp_comm (integrable_smul_kernel K v)]
  apply integral_congr_ae
  filter_upwards [Q.coeFn_compLp K] with x hx
  change v x • Q.compLp K x=Q (v x • K x)
  rw [hx,map_smul]

theorem synthesis_norm_le (K : Lp E 2 ν) : ‖synthesis K‖ ≤ ‖K‖ := by
  simpa only [synthesis,LinearIsometryEquiv.norm_map] using operator_norm_le K

theorem synthesis_continuous : Continuous (synthesis (ν:=ν) (E:=E)) :=
  ContinuousLinearMap.adjoint.continuous.comp operator_continuous

theorem synthesis_trace (K : Lp E 2 ν)
    (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ (Lp ℂ 2 ν)) :
    Summable (fun j => ‖synthesis K (c j)‖^2) ∧
      (∑' j, ‖synthesis K (c j)‖^2) ≤ ‖K‖^2 := by
  have hk := operator_trace K b
  have ha := HilbertTrace.adjoint_trace (operator K) b c hk.1
  exact ⟨ha.1,ha.2.trans_le hk.2⟩

/-- The Hilbert--Schmidt estimate holds for the actual adjoint kernel
operator followed by any bounded noise factor. -/
theorem synthesis_right_trace {G Kidx : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (K : Lp E 2 ν) (R : G →L[ℂ] Lp ℂ 2 ν)
    (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ (Lp ℂ 2 ν))
    (g : HilbertBasis Kidx ℂ G) :
    Summable (fun k => ‖((synthesis K).comp R) (g k)‖^2) ∧
      (∑' k, ‖((synthesis K).comp R) (g k)‖^2) ≤ ‖R‖^2*‖K‖^2 := by
  have hk := synthesis_trace K b c
  have hh := HilbertTrace.right_comp (synthesis K) R c b g hk.1
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left hk.2 (sq_nonneg _))⟩

/-- Strong measurability of each right-factor column suffices. There is
no operator-norm measurability assumption on the random noise factor. -/
theorem synthesis_column_measurable {W G : Type*} [MeasurableSpace W]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace (Lp E 2 ν)] [BorelSpace (Lp E 2 ν)]
    [MeasurableSpace (Lp ℂ 2 ν)] [BorelSpace (Lp ℂ 2 ν)]
    [SecondCountableTopology (Lp E 2 ν)] [SecondCountableTopology (Lp ℂ 2 ν)]
    {K : W → Lp E 2 ν} {R : W → G →L[ℂ] Lp ℂ 2 ν}
    (hK : Measurable K) (d : G) (hR : Measurable (fun ω => R ω d)) :
    Measurable (fun ω => (synthesis (K ω)) (R ω d)) := by
  have hc : Continuous (fun p : Lp E 2 ν × Lp ℂ 2 ν => synthesis p.1 p.2) :=
    (synthesis_continuous.comp continuous_fst).clm_apply continuous_snd
  exact hc.measurable.comp (hK.prodMk hR)

/-- Integrability and the sharp expected trace bound are consequences
of the actual random kernel mass. The kernel and noise factor may share
arbitrary randomness. -/
theorem expected_synthesis_right_trace_bound
    {W G Kidx : Type*} [MeasurableSpace W] (P : Measure W)
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [Countable Kidx]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace (Lp E 2 ν)] [BorelSpace (Lp E 2 ν)]
    [MeasurableSpace (Lp ℂ 2 ν)] [BorelSpace (Lp ℂ 2 ν)]
    [SecondCountableTopology (Lp E 2 ν)] [SecondCountableTopology (Lp ℂ 2 ν)]
    (K : W → Lp E 2 ν) (R : W → G →L[ℂ] Lp ℂ 2 ν)
    (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ (Lp ℂ 2 ν))
    (g : HilbertBasis Kidx ℂ G) (hK : Measurable K)
    (hRmeas : ∀ k, Measurable (fun ω => R ω (g k)))
    {C A : ℝ} (hC : 0 ≤ C) (hR : ∀ ω, ‖R ω‖^2 ≤ C)
    (hInt : Integrable (fun ω => ‖K ω‖^2) P)
    (hA : (∫ ω, ‖K ω‖^2 ∂P) ≤ A) :
    Integrable (fun ω => ∑' k, ‖((synthesis (K ω)).comp (R ω)) (g k)‖^2) P ∧
      (∫ ω, ∑' k, ‖((synthesis (K ω)).comp (R ω)) (g k)‖^2 ∂P) ≤ C*A := by
  have hm : Measurable (fun ω => ∑' k, ‖((synthesis (K ω)).comp (R ω)) (g k)‖^2) :=
    Measurable.tsum (fun k => (synthesis_column_measurable hK (g k) (hRmeas k)).norm.pow_const (2:ℕ))
  have hb (ω : W) : (∑' k, ‖((synthesis (K ω)).comp (R ω)) (g k)‖^2) ≤ C*‖K ω‖^2 :=
    (synthesis_right_trace (K ω) (R ω) b c g).2.trans
      (mul_le_mul_of_nonneg_right (hR ω) (sq_nonneg _))
  have hi : Integrable (fun ω => ∑' k, ‖((synthesis (K ω)).comp (R ω)) (g k)‖^2) P := by
    apply (hInt.const_mul C).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
      exact hb ω)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, C*‖K ω‖^2 ∂P := integral_mono hi (hInt.const_mul C) hb
    _ = C*∫ ω, ‖K ω‖^2 ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hA hC

end SHE.KernelOperator
