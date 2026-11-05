module

public import SHEStochastic.PastedLinearHeatMartingale
public import SHEStochastic.KernelUniformMoment
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.PastedLinearHeatIntegrability
open MeasureTheory ProbabilityTheory StoppedPathPasting PastedLinearHeatFunctional
open scoped NNReal ENNReal

variable {E Ω : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [Module ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  (H : ℝ≥0) (ell : E →L[ℝ] ℝ) (lam : ℝ)
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → Path H E) (exit : Ω → Time H) (hX : Measurable X) (hr : Measurable exit)
  (κ : Kernel E (Path H E)) [IsMarkovKernel κ]

local notation "ν" => StoppedContinuationMeasure.joint H X exit hX hr μ κ
local notation "pastePath" => StoppedContinuationMeasure.value H X exit

/-- Conditional fourth moments of a fixed path envelope remain fourth
moments after sampling the continuation at the random exit state. -/
theorem future_envelope_memLp (C : ℝ≥0∞) (hC : C < ⊤)
    (hbound : ∀ᵐ ω ∂μ, (∫⁻ y, ENNReal.ofReal ((envelope H ell lam y)^4)
      ∂κ (StoppedContinuationMeasure.state H X exit ω)) ≤ C) :
    MemLp (fun z : Ω × Path H E ↦ envelope H ell lam z.2) 4 ν := by
  exact KernelUniformMoment.memLp_nonneg_nat μ
    (StoppedContinuationMeasure.continuation H X exit hX hr κ) 4 (by norm_num) _
    ((continuous_envelope H ell lam).measurable.comp measurable_snd)
    (fun z ↦ norm_nonneg _) C hC hbound

/-- A deterministic bound on the stopped prefix gives integrability of
every past-tested prefix increment on the actual enlarged space. -/
theorem pre_integrable (D : ℝ)
    (hbound : ∀ᵐ ω ∂μ, ∀ t : Time H, t ≤ exit ω → ‖value H ell lam (X ω) t‖ ≤ D)
    (s t : Time H) (test : BoundedContinuousFunction (Path H E) ℝ) :
    Integrable (fun z : Ω × Path H E ↦ test (pastePath z)*
      (value H ell lam (X z.1) (pastTime H (exit z.1) t)-
        value H ell lam (X z.1) (pastTime H (exit z.1) s))) ν := by
  have hpre (q : Time H) : Measurable (fun z : Ω × Path H E ↦
      value H ell lam (X z.1) (pastTime H (exit z.1) q)) :=
    (continuous_value H ell lam).measurable.comp ((hX.comp measurable_fst).prodMk
      ((continuous_pastTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const)))
  apply (integrable_const (‖test‖*(D+D))).mono'
    ((test.continuous.measurable.comp (StoppedContinuationMeasure.measurable_value H X exit hX hr)).mul
      ((hpre t).sub (hpre s))).aestronglyMeasurable
  have hp : MeasurePreserving (Prod.fst : Ω × Path H E → Ω) ν μ :=
    ⟨measurable_fst, Measure.fst_compProd μ _⟩
  have ha : ∀ᵐ z ∂ν, ∀ q : Time H, q ≤ exit z.1 → ‖value H ell lam (X z.1) q‖ ≤ D :=
    hp.quasiMeasurePreserving.ae hbound
  filter_upwards [ha] with z hz
  exact (norm_mul _ _).trans_le (mul_le_mul
    (test.norm_coe_le_norm _) ((norm_sub_le _ _).trans
      (add_le_add (hz _ (min_le_right _ _)) (hz _ (min_le_right _ _))))
        (norm_nonneg _) (norm_nonneg _))

/-- The future increment is dominated by twice its Borel path envelope.
The random integrating factor is bounded on the fixed time horizon. -/
theorem post_integrable (hlam : 0 ≤ lam)
    (hEnv : Integrable (fun z : Ω × Path H E ↦ envelope H ell lam z.2) ν)
    (s t : Time H) (test : BoundedContinuousFunction (Path H E) ℝ) :
    Integrable (fun z : Ω × Path H E ↦ test (pastePath z)*
      (Real.exp (lam*(exit z.1).val)*(value H ell lam z.2 (futureTime H (exit z.1) t)-
        value H ell lam z.2 (futureTime H (exit z.1) s)))) ν := by
  have hfut (q : Time H) : Measurable (fun z : Ω × Path H E ↦
      value H ell lam z.2 (futureTime H (exit z.1) q)) :=
    (continuous_value H ell lam).measurable.comp (measurable_snd.prodMk
      ((continuous_futureTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const)))
  have hd : Integrable (fun z : Ω × Path H E ↦
      value H ell lam z.2 (futureTime H (exit z.1) t)-
        value H ell lam z.2 (futureTime H (exit z.1) s)) ν := by
    apply (hEnv.add hEnv).mono' ((hfut t).sub (hfut s)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z ↦ (norm_sub_le _ _).trans
      (add_le_add (value_bound H ell lam _ _) (value_bound H ell lam _ _))
  have he : ∀ᵐ z : Ω × Path H E ∂ν, ‖Real.exp (lam*(exit z.1).val)‖ ≤ Real.exp (lam*H) :=
    Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (exit z.1).property.2 hlam)
  have hExp : Measurable (fun z : Ω × Path H E ↦ Real.exp (lam*(exit z.1).val)) :=
    (measurable_const.mul (measurable_subtype_coe.comp (hr.comp measurable_fst))).exp
  exact (hd.bdd_mul hExp.aestronglyMeasurable he).bdd_mul
    (test.continuous.measurable.comp (StoppedContinuationMeasure.measurable_value H X exit hX hr)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ test.norm_coe_le_norm _)

/-- The maximum of the pasted heat mode has the same fourth-moment
control. Only the stopped source prefix needs a deterministic bound. -/
theorem pasted_envelope_memLp (hlam : 0 ≤ lam) (D : ℝ)
    (hbound : ∀ᵐ ω ∂μ, ∀ t : Time H, t ≤ exit ω → ‖value H ell lam (X ω) t‖ ≤ D)
    (hinitial : ∀ᵐ ω ∂μ, ∀ᵐ y ∂κ (StoppedContinuationMeasure.state H X exit ω),
      y (origin H) = StoppedContinuationMeasure.state H X exit ω)
    (hEnv : MemLp (fun z : Ω × Path H E ↦ envelope H ell lam z.2) 4 ν) :
    MemLp (fun z : Ω × Path H E ↦ envelope H ell lam (pastePath z)) 4 ν := by
  have hp : MeasurePreserving (Prod.fst : Ω × Path H E → Ω) ν μ :=
    ⟨measurable_fst, Measure.fst_compProd μ _⟩
  apply ((memLp_const D).add (hEnv.const_mul (Real.exp (lam*H)))).mono'
    (((continuous_envelope H ell lam).measurable.comp
      (StoppedContinuationMeasure.measurable_value H X exit hX hr)).aestronglyMeasurable)
  filter_upwards [hp.quasiMeasurePreserving.ae hbound,
    StoppedContinuationMeasure.matching_initial_of_ae H X exit hX hr μ κ hinitial] with z hz hj
  obtain ⟨t, ht⟩ := envelope_attained H ell lam (pastePath z)
  change ‖envelope H ell lam (pastePath z)‖ ≤ D+Real.exp (lam*H)*envelope H ell lam z.2
  rw [Real.norm_of_nonneg (show 0 ≤ envelope H ell lam (pastePath z) from norm_nonneg _), ht]
  change ‖value H ell lam (paste H (exit z.1) (X z.1) z.2) t‖ ≤ _
  rw [value_paste H ell lam (exit z.1) t (X z.1) z.2 hj]
  apply (norm_add_le _ _).trans (add_le_add (hz _ (min_le_right _ _)) ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (exit z.1).property.2 hlam))
    (value_bound H ell lam _ _) (norm_nonneg _) (Real.exp_pos _).le

end SHEStochastic.PastedLinearHeatIntegrability
