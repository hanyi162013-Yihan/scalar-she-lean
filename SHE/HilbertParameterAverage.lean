module

public import SHE.WeightedSpatialMoments
public import SHE.WeightedSFiniteMoments
public import SHE.TerminalItoFubini

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.HilbertParameterAverage
open Set Filter MeasureTheory Real PredictableL2
open scoped ENNReal NNReal
variable {Ω P E : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Pointwise RMS bounds give the genuine joint Bochner integrability
needed before changing the old-parameter and probability integrals.
The old-parameter envelope need only be L1, not L2. -/
theorem joint_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure P) [SFinite ν] (F : P × Ω → E) (hF : Measurable F)
    (A : P → ℝ) (hA : Integrable A ν) (hA0 : 0 ≤ᵐ[ν] A)
    (hi : ∀ᵐ p ∂ν,Integrable (fun ω => ‖F (p,ω)‖^2) μ)
    (hb : ∀ᵐ p ∂ν,(∫ ω,‖F (p,ω)‖^2 ∂μ) ≤ A p^2) :
    Integrable F (ν.prod μ) := by
  have hsections : ∀ᵐ p ∂ν,Integrable (fun ω => F (p,ω)) μ ∧
      (∫ ω,‖F (p,ω)‖ ∂μ) ≤ A p := by
    filter_upwards [hi,hb,hA0] with p hp hpb hpa
    change 0 ≤ A p at hpa
    have hf := (memLp_two_iff_integrable_sq_norm
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hp
    have hn : ‖hf.toLp (fun ω => F (p,ω))‖^2=∫ ω,‖F (p,ω)‖^2 ∂μ := by
      rw [realLp_norm_sq]
      exact integral_congr_ae (hf.coeFn_toLp.mono (fun ω hω => congrArg (fun z : E => ‖z‖^2) hω))
    have hnorm : ‖hf.toLp (fun ω => F (p,ω))‖ ≤ A p := by
      nlinarith [norm_nonneg (hf.toLp (fun ω => F (p,ω)))]
    have hL1 := LpIntegralFubini.integral_norm_le_norm μ (hf.toLp (fun ω => F (p,ω)))
    have he : (∫ ω,‖hf.toLp (fun ω => F (p,ω)) ω‖ ∂μ)=∫ ω,‖F (p,ω)‖ ∂μ :=
      integral_congr_ae (hf.coeFn_toLp.mono (fun ω hω => congrArg norm hω))
    rw [he] at hL1
    simp only [probReal_univ,sqrt_one,one_mul] at hL1
    exact ⟨hf.integrable (by norm_num : (1:ENNReal) ≤ 2),hL1.trans hnorm⟩
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨hsections.mono (fun _ h => h.1),?_⟩
  have hm : StronglyMeasurable (fun p => ∫ ω,‖F (p,ω)‖ ∂μ) :=
    hF.norm.stronglyMeasurable.integral_prod_right' (ν:=μ)
  apply hA.mono' hm.aestronglyMeasurable
  filter_upwards [hsections] with p hp
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact hp.2

/-- Hilbert-valued Minkowski in the old parameters, before the final
stochastic square. No separability of the global probability L2 space
and no independence of the parameterized columns is required. -/
theorem energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure P) [SFinite ν] (F : P × Ω → E) (hF : Measurable F)
    (A : P → ℝ) (hAm : Measurable A) (hAi : Integrable A ν) (hA0 : ∀ p,0 ≤ A p)
    (hi : ∀ᵐ p ∂ν,Integrable (fun ω => ‖F (p,ω)‖^2) μ)
    (hb : ∀ᵐ p ∂ν,(∫ ω,‖F (p,ω)‖^2 ∂μ) ≤ A p^2) :
    Integrable F (ν.prod μ) ∧
      Integrable (fun ω => ‖∫ p,F (p,ω) ∂ν‖^2) μ ∧
      (∫ ω,‖∫ p,F (p,ω) ∂ν‖^2 ∂μ) ≤ (∫ p,A p ∂ν)^2 := by
  have hFn : Measurable (fun z : Ω × P => ‖F (z.2,z.1)‖) := (hF.comp measurable_swap).norm
  have hin : ∀ᵐ p ∂ν,Integrable (fun ω => |‖F (p,ω)‖|^(2*1)) μ := by
    simpa only [abs_of_nonneg (norm_nonneg _),Nat.mul_one] using hi
  have hbn : ∀ᵐ p ∂ν,(∫ ω,|‖F (p,ω)‖|^(2*1) ∂μ) ≤ 1*(A p)^(2*1) := by
    simpa only [abs_of_nonneg (norm_nonneg _),Nat.mul_one,one_mul] using hb
  have hh := WeightedSFiniteMoments.nonnegative_envelope μ ν _ hFn A hAm hAi hA0
    1 (by norm_num) 1 (by norm_num) hin hbn
  have hg : Integrable (fun ω => (∫ p,‖F (p,ω)‖ ∂ν)^2) μ := by
    simpa only [Nat.mul_one,sq_abs] using hh.1
  have hbound : ∀ ω,‖∫ p,F (p,ω) ∂ν‖^2 ≤ (∫ p,‖F (p,ω)‖ ∂ν)^2 := fun ω =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2
  have hm : Measurable (fun ω => ‖∫ p,F (p,ω) ∂ν‖^2) :=
    hF.stronglyMeasurable.integral_prod_left'.measurable.norm.pow_const 2
  have hactual : Integrable (fun ω => ‖∫ p,F (p,ω) ∂ν‖^2) μ := by
    apply hg.mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)];exact hbound ω)
  refine ⟨joint_integrable μ ν F hF A hAi (ae_of_all _ hA0) hi hb,hactual,?_⟩
  exact (integral_mono hactual hg hbound).trans
    (by simpa only [Nat.mul_one,sq_abs,one_mul] using hh.2)

/-- Averaging over old time parameters preserves the actual predictable
sigma algebra. This constructs the averaged field before the terminal
Itô square, rather than assuming a stochastic Fubini operation. -/
theorem average_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (ν : Measure P) [SFinite ν] (F : P × (ℝ≥0 × Ω) → E)
    (hF : @Measurable (P × (ℝ≥0 × Ω)) E
      (MeasurableSpace.prod (inferInstance : MeasurableSpace P) 𝓕.predictable)
      (inferInstance : MeasurableSpace E) F) :
    StronglyMeasurable[𝓕.predictable] (fun z => ∫ p,F (p,z) ∂ν) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact hF.stronglyMeasurable.integral_prod_left'

end SHE.HilbertParameterAverage
