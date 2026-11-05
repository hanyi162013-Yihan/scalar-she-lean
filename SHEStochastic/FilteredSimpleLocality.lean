/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Deterministic step/locality proofs reused from formal-mathfin,
3c41aee9bf2d9743f9e66b439f90d1635843d2d2, ItoIntegralBrownian.lean and
ItoIntegralLocality.lean. They are generalized to an arbitrary supplied
filtration. No Brownian or other stochastic theorem is an assumption.
-/
module

public import SHEStochastic.FiniteScalarIto
public import MathFin.Foundations.ItoIntegralLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.FilteredSimpleLocality
open MeasureTheory ProbabilityTheory Filter FilteredItoL2 FilteredItoCLM
open MathFin (afterFactor abs_afterFactor_le mulBddCLM)
open scoped NNReal ENNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

noncomputable def stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[F a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) :
    TBoundedSP (𝓖 := F) T hBmeas :=
  ⟨{ valueBot := 0
     value := Finsupp.single (a, b) φ
     le_of_mem_support_value := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       exact hab
     measurable_valueBot := measurable_const
     measurable_value' := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same]; exact hφ
     bounded_valueBot := ⟨0, by simp⟩
     bounded_value := ⟨M, fun p hp ω ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same, Real.norm_eq_abs]; exact hφM ω⟩ },
   fun p hp ↦ by
     obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
     exact hbT⟩

/-- The terminal Itô integral of a single step is `φ·(B_b − B_a)`. -/
lemma itoSimple_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[F a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) (ω : Ω) :
    itoSimple hBmeas (stepSP hBmeas hab hbT hφ hφM).val ω = φ ω * (B b ω - B a ω) := by
  rw [itoSimple_apply]
  show (Finsupp.single (a, b) φ).sum (fun p v ↦ v ω * (B p.2 ω - B p.1 ω))
      = φ ω * (B b ω - B a ω)
  rw [Finsupp.sum_single_index (by simp)]


lemma itoSimple_sum (hBmeas : ∀ t, Measurable (B t)) {ι' : Type*} (s : Finset ι')
    (V : ι' → SimpleProcess ℝ (F)) :
    itoSimple hBmeas (∑ i ∈ s, V i) = ∑ i ∈ s, itoSimple hBmeas (V i) := by
  classical
  induction s using Finset.induction with
  | empty => funext ω; simp [itoSimple]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, itoSimple_add, ih]


lemma measurable_afterFactor {a : ℝ≥0} {Z : Ω → ℝ}
    (hZm : Measurable[F a] Z) :
    Measurable[F.predictable] (afterFactor a Z) := by
  set 𝓕 := F
  intro S hS
  have hIoi : MeasurableSet[𝓕.predictable] (Set.Ioi a ×ˢ (Z ⁻¹' S)) :=
    MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (hZm hS)
  have hoff : MeasurableSet[𝓕.predictable] ((Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ) :=
    (MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (i := a)
      MeasurableSet.univ).compl
  by_cases h0 : (0 : ℝ) ∈ S
  · have hset : afterFactor a Z ⁻¹' S
        = Set.Ioi a ×ˢ (Z ⁻¹' S) ∪ (Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_Ioi,
        Set.mem_compl_iff, Set.mem_univ, and_true]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi.union hoff
  · have hset : afterFactor a Z ⁻¹' S = Set.Ioi a ×ˢ (Z ⁻¹' S) := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_prod, Set.mem_Ioi]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi


noncomputable def smulAdaptedCLM (T a : ℝ≥0)
    (Z : Ω → ℝ) (hZm : Measurable[F a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) :
    Lp ℝ 2 (FiniteScalarIto.inputMeasure F μ T) →L[ℝ]
      Lp ℝ 2 (FiniteScalarIto.inputMeasure F μ T) :=
  mulBddCLM (FiniteScalarIto.inputMeasure F μ T) (measurable_afterFactor hZm)
    (abs_afterFactor_le hZb)


lemma coe_simpleProcess_sum {ι' : Type*} (hBmeas : ∀ t, Measurable (B t))
    (s : Finset ι') (W : ι' → SimpleProcess ℝ (F))
    (t : ℝ≥0) (ω : Ω) : ⇑(∑ i ∈ s, W i) t ω = ∑ i ∈ s, ⇑(W i) t ω := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, SimpleProcess.coe_add]
      simp [ih]

/-- A single step evaluates to the indicator of its rectangle. -/
lemma coe_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a' b : ℝ≥0}
    (hab : a' ≤ b) (hbT : b ≤ T) {ψ : Ω → ℝ}
    (hψm : Measurable[F a'] ψ) {M : ℝ} (hψM : ∀ ω, |ψ ω| ≤ M)
    (t : ℝ≥0) (ω : Ω) :
    ⇑(stepSP hBmeas hab hbT hψm hψM : TBoundedSP (𝓖 := F) T hBmeas).val t ω
      = (Set.Ioc a' b).indicator (fun _ ↦ ψ ω) t := by
  rw [SimpleProcess.apply_eq]
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ (stepSP hBmeas hab hbT hψm hψM :
        TBoundedSP (𝓖 := F) T hBmeas).val.valueBot ω) t = 0 := by
    simp [stepSP]
  rw [hbot, zero_add]
  show (Finsupp.single (a', b) ψ).sum
      (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) t) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- **`V` restarted at `a`, scaled by `Z`.** Each rectangle `(p.1, p.2]` of `V` is
cut down to `(a ⊔ p.1, p.2]` (empty, and dropped, when that is degenerate) and its
coefficient is multiplied by `Z`. The result is again a `T`-bounded simple process:
the new coefficient `Z·V(p)` is `𝓕_{a ⊔ p.1}`-measurable because `Z` is
`𝓕_a`-measurable and `V(p)` is `𝓕_{p.1}`-measurable — this is the one place where
`a ≤ a ⊔ p.1` earns the support hypothesis its keep. -/
noncomputable def afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[F a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓖 := F) T hBmeas) : TBoundedSP (𝓖 := F) T hBmeas :=
  ∑ p ∈ V.val.value.support.attach,
    if h : a ⊔ p.val.1 ≤ p.val.2 then
      stepSP hBmeas h (V.property p.val p.property)
        (φ := fun ω ↦ Z ω * V.val.value p.val ω)
        ((hZm.mono (F.mono le_sup_left) le_rfl).mul
          ((V.val.measurable_value p.val).mono
            (F.mono le_sup_right) le_rfl))
        (M := C * V.val.valueBound)
        (fun ω ↦ by
          rw [abs_mul]
          exact mul_le_mul (hZb ω)
            (by rw [← Real.norm_eq_abs]; exact V.val.value_le_valueBound p.val ω)
            (abs_nonneg _) ((abs_nonneg (Z ω)).trans (hZb ω)))
    else 0

/-- **The defining pointwise identity of `afterStepSP`**: off the time origin it is
`𝟙_{a < t}·Z·V`. -/
lemma coe_afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[F a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓖 := F) T hBmeas) {t : ℝ≥0} (ht : t ≠ 0) (ω : Ω) :
    ⇑(afterStepSP T a hBmeas Z hZm C hZb V).val t ω
      = afterFactor a Z (t, ω) * ⇑V.val t ω := by
  have htbot : t ∉ ({(⊥ : ℝ≥0)} : Set ℝ≥0) := by
    simp only [Set.mem_singleton_iff, NNReal.bot_eq_zero]
    exact ht
  have hV : ⇑V.val t ω
      = ∑ p ∈ V.val.value.support,
          (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.val.value p ω) t := by
    rw [SimpleProcess.apply_eq, Set.indicator_of_notMem htbot, zero_add, Finsupp.sum]
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, coe_simpleProcess_sum hBmeas, hV, Finset.mul_sum,
    ← Finset.sum_attach V.val.value.support
      (fun q ↦ afterFactor a Z (t, ω) * (Set.Ioc q.1 q.2).indicator
        (fun _ ↦ V.val.value q ω) t)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, coe_stepSP]
    simp only [afterFactor]
    by_cases hat : a < t
    · have hmem : t ∈ Set.Ioc (a ⊔ p.val.1) p.val.2 ↔ t ∈ Set.Ioc p.val.1 p.val.2 := by
        simp only [Set.mem_Ioc, sup_lt_iff]
        exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨hat, h.1⟩, h.2⟩⟩
      by_cases hin : t ∈ Set.Ioc p.val.1 p.val.2
      · rw [Set.indicator_of_mem (hmem.mpr hin), Set.indicator_of_mem hin, if_pos hat]
      · rw [Set.indicator_of_notMem (fun hc ↦ hin (hmem.mp hc)), Set.indicator_of_notMem hin,
          mul_zero]
    · rw [if_neg hat, zero_mul]
      exact Set.indicator_of_notMem (fun hc ↦ hat (lt_of_le_of_lt le_sup_left hc.1)) _
  · rw [dif_neg hle]
    have hzero : ⇑((0 : TBoundedSP (𝓖 := F) T hBmeas).val) t ω = 0 := by simp
    rw [hzero, eq_comm]
    simp only [afterFactor]
    by_cases hat : a < t
    · rw [Set.indicator_of_notMem (fun hc ↦ hle (sup_le (hat.le.trans hc.2) (hc.1.le.trans hc.2))),
        mul_zero]
    · rw [if_neg hat, zero_mul]


lemma itoSimple_afterStepSP_eq (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[F a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓖 := F) T hBmeas) (ω : Ω) :
    FilteredItoL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = ∑ p ∈ V.val.value.support.attach,
          if _h : a ⊔ p.val.1 ≤ p.val.2 then
            Z ω * V.val.value p.val ω * (B p.val.2 ω - B (a ⊔ p.val.1) ω) else 0 := by
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, itoSimple_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, dif_pos hle, itoSimple_stepSP]
  · rw [dif_neg hle, dif_neg hle]
    simp [FilteredItoL2.itoSimple]

/-- **The scaling passes through the elementary integral**: `Z` factors out of the
finite increment sum. -/
lemma itoSimple_afterStepSP_smul (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[F a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓖 := F) T hBmeas) (ω : Ω) :
    FilteredItoL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = Z ω * FilteredItoL2.itoSimple hBmeas
          (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
            (fun _ ↦ abs_one.le) V).val ω := by
  rw [itoSimple_afterStepSP_eq, itoSimple_afterStepSP_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, dif_pos hle]; ring
  · rw [dif_neg hle, dif_neg hle, mul_zero]


end SHEStochastic.FilteredSimpleLocality
