module

public import SHEStochastic.PastedHeatProductMartingale
public import SHEStochastic.PastedLinearHeatIntegrability
public import SHEStochastic.QuadraticMomentBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.PastedHeatProductIntegrability
open MeasureTheory ProbabilityTheory StoppedPathPasting
open PastedLinearHeatFunctional PastedHeatProductMartingale
open scoped NNReal ENNReal

variable {E Z : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]
  (H : ℝ≥0)

/-- Measurable random-time readings are controlled by the same fixed
Borel observable; no optional evaluation theorem is assumed. -/
theorem linear_memLp (ell : E →L[ℝ] ℝ) (lam : ℝ) (ν : Measure Z)
    (Y : Z → Path H E) (hY : Measurable Y) (q : Z → Time H) (hq : Measurable q)
    (A : Z → ℝ) (hA : MemLp A 4 ν) (hbound : ∀ᵐ z ∂ν, ‖value H ell lam (Y z) (q z)‖ ≤ A z) :
    MemLp (fun z ↦ value H ell lam (Y z) (q z)) 4 ν :=
  hA.mono' ((continuous_value H ell lam).measurable.comp (hY.prodMk hq)).aestronglyMeasurable hbound

theorem covariance_memLp (rate : ℝ) (hrate : 0 ≤ rate) (b : BoundedContinuousFunction E ℝ)
    (ν : Measure Z) [IsFiniteMeasure ν] (Y : Z → Path H E) (hY : Measurable Y)
    (q : Z → Time H) (hq : Measurable q) :
    MemLp (fun z ↦ PastedHeatCovariance.value H rate hrate b (Y z) (q z)) 2 ν :=
  MemLp.of_bound ((PastedHeatCovariance.continuous_value H rate hrate b).measurable.comp
    (hY.prodMk hq)).aestronglyMeasurable
    (‖PathIntegratedCovariance.exponential H rate hrate‖*‖b‖*H)
    (Filter.Eventually.of_forall fun z ↦ PastedHeatCovariance.norm_bound H rate hrate b _ _)

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → Path H E) (exit : Ω → Time H) (hX : Measurable X) (hr : Measurable exit)
  (κ : Kernel E (Path H E)) [IsMarkovKernel κ]

local notation "ν" => StoppedContinuationMeasure.joint H X exit hX hr μ κ

/-- Any integrable term remains integrable after the bounded past test
and the bounded random exponential factor at the join. -/
theorem weighted (rate : ℝ) (hrate : 0 ≤ rate) (f : Ω × Path H E → ℝ) (hf : Integrable f ν)
    (test : BoundedContinuousFunction (Path H E) ℝ) :
    Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      (Real.exp (rate*(exit z.1).val)*f z)) ν := by
  have he : Measurable (fun z : Ω × Path H E ↦ Real.exp (rate*(exit z.1).val)) :=
    (measurable_const.mul (measurable_subtype_coe.comp (hr.comp measurable_fst))).exp
  have hb : ∀ᵐ z : Ω × Path H E ∂ν, ‖Real.exp (rate*(exit z.1).val)‖ ≤ Real.exp (rate*H) :=
    Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (exit z.1).property.2 hrate)
  exact (hf.bdd_mul he.aestronglyMeasurable hb).bdd_mul
    (test.continuous.measurable.comp (StoppedContinuationMeasure.measurable_value H X exit hX hr)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ test.norm_coe_le_norm _)

/-- Fourth moments of the source prefix and the conditional future
maxima discharge every integrability premise of product pasting. -/
theorem parts (ell₁ ell₂ : E →L[ℝ] ℝ) (lam₁ lam₂ : ℝ) (h₁ : 0 ≤ lam₁) (h₂ : 0 ≤ lam₂)
    (b : BoundedContinuousFunction E ℝ) (A₁ A₂ : Ω → ℝ) (hA₁ : MemLp A₁ 4 μ) (hA₂ : MemLp A₂ 4 μ)
    (hpre₁ : ∀ᵐ ω ∂μ, ∀ t : Time H, t ≤ exit ω → ‖value H ell₁ lam₁ (X ω) t‖ ≤ A₁ ω)
    (hpre₂ : ∀ᵐ ω ∂μ, ∀ t : Time H, t ≤ exit ω → ‖value H ell₂ lam₂ (X ω) t‖ ≤ A₂ ω)
    (hE₁ : MemLp (fun z : Ω × Path H E ↦ envelope H ell₁ lam₁ z.2) 4 ν)
    (hE₂ : MemLp (fun z : Ω × Path H E ↦ envelope H ell₂ lam₂ z.2) 4 ν)
    (s t : Time H) (test : BoundedContinuousFunction (Path H E) ℝ) :
    Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      prefixPart H ell₁ ell₂ lam₁ lam₂ (add_nonneg h₁ h₂) b X exit s t z.1) ν ∧
    Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      productPart H ell₁ ell₂ lam₁ lam₂ (add_nonneg h₁ h₂) b exit s t z) ν ∧
    Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      crossPart H ell₁ ell₂ lam₁ lam₂ X exit s t z) ν ∧
    Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      crossPart H ell₂ ell₁ lam₂ lam₁ X exit s t z) ν := by
  have hp : MeasurePreserving (Prod.fst : Ω × Path H E → Ω) ν μ :=
    ⟨measurable_fst, Measure.fst_compProd μ _⟩
  have hSrc (ell : E →L[ℝ] ℝ) (lam : ℝ) (A : Ω → ℝ) (ha : MemLp A 4 μ)
      (hb : ∀ᵐ ω ∂μ, ∀ q : Time H, q ≤ exit ω → ‖value H ell lam (X ω) q‖ ≤ A ω)
      (q : Ω × Path H E → Time H) (hq : Measurable q) (hbefore : ∀ z, q z ≤ exit z.1) :
      MemLp (fun z ↦ value H ell lam (X z.1) (q z)) 4 ν := by
    apply linear_memLp H ell lam ν (fun z ↦ X z.1) (hX.comp measurable_fst) q hq
      (A ∘ Prod.fst) (ha.comp_measurePreserving hp)
    exact (hp.quasiMeasurePreserving.ae hb).mono fun z hz ↦ hz (q z) (hbefore z)
  have hFut (ell : E →L[ℝ] ℝ) (lam : ℝ)
      (he : MemLp (fun z : Ω × Path H E ↦ envelope H ell lam z.2) 4 ν)
      (q : Time H) : MemLp (fun z : Ω × Path H E ↦
        value H ell lam z.2 (futureTime H (exit z.1) q)) 4 ν :=
    linear_memLp H ell lam ν Prod.snd measurable_snd _
      ((continuous_futureTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const)) _ he
      (Filter.Eventually.of_forall fun z ↦ value_bound H ell lam _ _)
  have hPast (ell : E →L[ℝ] ℝ) (lam : ℝ) (A : Ω → ℝ) (ha : MemLp A 4 μ)
      (hb : ∀ᵐ ω ∂μ, ∀ q : Time H, q ≤ exit ω → ‖value H ell lam (X ω) q‖ ≤ A ω)
      (q : Time H) : MemLp (fun z : Ω × Path H E ↦
        value H ell lam (X z.1) (pastTime H (exit z.1) q)) 4 ν :=
    hSrc ell lam A ha hb _
      ((continuous_pastTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const))
      (fun z ↦ min_le_right _ _)
  have hJoin₁ := hSrc ell₁ lam₁ A₁ hA₁ hpre₁ (fun z ↦ exit z.1) (hr.comp measurable_fst) (fun z ↦ le_rfl)
  have hJoin₂ := hSrc ell₂ lam₂ A₂ hA₂ hpre₂ (fun z ↦ exit z.1) (hr.comp measurable_fst) (fun z ↦ le_rfl)
  have hProduct (Y : Ω × Path H E → Path H E) (hy : Measurable Y) (q : Ω × Path H E → Time H)
      (hq : Measurable q) (hm₁ : MemLp (fun z ↦ value H ell₁ lam₁ (Y z) (q z)) 4 ν)
      (hm₂ : MemLp (fun z ↦ value H ell₂ lam₂ (Y z) (q z)) 4 ν) :
      MemLp (fun z ↦ PastedHeatProductFunctional.value H ell₁ ell₂ lam₁ lam₂ (add_nonneg h₁ h₂) b (Y z) (q z)) 2 ν :=
    (QuadraticMomentBounds.product_memLp ν hm₁ hm₂).sub (covariance_memLp H _ _ b ν Y hy q hq)
  have hPre (q : Time H) := hProduct (fun z ↦ X z.1) (hX.comp measurable_fst) _
    ((continuous_pastTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const))
    (hPast ell₁ lam₁ A₁ hA₁ hpre₁ q) (hPast ell₂ lam₂ A₂ hA₂ hpre₂ q)
  have hPost (q : Time H) := hProduct Prod.snd measurable_snd _
    ((continuous_futureTime H).measurable.comp ((hr.comp measurable_fst).prodMk measurable_const))
    (hFut ell₁ lam₁ hE₁ q) (hFut ell₂ lam₂ hE₂ q)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := weighted H μ X exit hX hr κ 0 (by norm_num) _
      (((hPre t).sub (hPre s)).integrable (by norm_num)) test
    simpa only [prefixPart, Function.comp_apply, Pi.sub_apply, zero_mul, Real.exp_zero, one_mul] using hh
  · exact weighted H μ X exit hX hr κ (lam₁+lam₂) (add_nonneg h₁ h₂) _
      (((hPost t).sub (hPost s)).integrable (by norm_num)) test
  · have hm : MemLp (fun z ↦ value H ell₁ lam₁ (X z.1) (exit z.1)*
        (value H ell₂ lam₂ z.2 (futureTime H (exit z.1) t)-
          value H ell₂ lam₂ z.2 (futureTime H (exit z.1) s))) 2 ν :=
      QuadraticMomentBounds.product_memLp ν hJoin₁ ((hFut ell₂ lam₂ hE₂ t).sub (hFut ell₂ lam₂ hE₂ s))
    convert weighted H μ X exit hX hr κ lam₂ h₂ _ (hm.integrable (by norm_num)) test using 1
    funext z
    unfold crossPart
    ring
  · have hm : MemLp (fun z ↦ value H ell₂ lam₂ (X z.1) (exit z.1)*
        (value H ell₁ lam₁ z.2 (futureTime H (exit z.1) t)-
          value H ell₁ lam₁ z.2 (futureTime H (exit z.1) s))) 2 ν :=
      QuadraticMomentBounds.product_memLp ν hJoin₂ ((hFut ell₁ lam₁ hE₁ t).sub (hFut ell₁ lam₁ hE₁ s))
    convert weighted H μ X exit hX hr κ lam₁ h₁ _ (hm.integrable (by norm_num)) test using 1
    funext z
    unfold crossPart
    ring

end SHEStochastic.PastedHeatProductIntegrability
