/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Generalized from formal-mathfin at 3c41aee9bf2d9743f9e66b439f90d1635843d2d2,
ItoIntegralCLM.lean. Predictable-simple density and completion are reused
for an arbitrary filtration; only the underlying increment isometry changes.
-/
module

public import MathFin.Foundations.ItoIntegralCLM
public import SHEStochastic.FilteredItoL2

@[expose] public section

namespace SHEStochastic.FilteredItoCLM

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace Topology
open MathFin
open MathFin.ItoIntegralCLM (timeMeasure_T)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}

noncomputable def trimMeasure_T (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :=
  ((timeMeasure_T T).prod μ).trim
    𝓖.predictable_le_prod

def predictableRect (hBmeas : ∀ t, Measurable (B t)) :
    Set (Set (ℝ≥0 × Ω)) :=
  𝓖.predictableRectangles

lemma isPiSystem_predictableRect (hBmeas : ∀ t, Measurable (B t)) :
    IsPiSystem (predictableRect (𝓖 := 𝓖) (mΩ := mΩ) hBmeas) :=
  (MeasureTheory.Filtration.isSetSemiring_predictableRectangles _).isPiSystem

theorem generateFrom_predictableRect (hBmeas : ∀ t, Measurable (B t)) :
    MeasurableSpace.generateFrom (predictableRect (𝓖 := 𝓖) (mΩ := mΩ) hBmeas) =
      𝓖.predictable := by
  apply le_antisymm
  · -- ≤: every basic rectangle is predictable-measurable
    apply MeasurableSpace.generateFrom_le
    rintro S (⟨F₀, hF₀, rfl⟩ | ⟨a, b, _hab, F, hF, rfl⟩)
    · -- `{0} ×ˢ F₀ = {⊥} ×ˢ F₀` (`(⊥ : ℝ≥0) = 0` by `rfl`)
      exact MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓖) hF₀
    · exact MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓖) a b hF
  · -- ≥: the predictable σ-algebra is contained in `generateFrom predictableRect (𝓖 := 𝓖)`
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom
        (MeasureTheory.Filtration.singletonBot_prod_mem_predictableRectangles _ hA)
    · intro i A hA
      obtain ⟨seq, _hmono, htends⟩ :=
        Filter.exists_seq_monotone_tendsto_atTop_atTop ℝ≥0
      have h_Ioi : (Set.Ioi i : Set ℝ≥0) = ⋃ n : ℕ, Set.Ioc i (seq n) := by
        ext s
        simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
        refine ⟨fun his ↦ ?_, fun ⟨_, h, _⟩ ↦ h⟩
        rw [Filter.tendsto_atTop_atTop] at htends
        obtain ⟨n, hn⟩ := htends s
        exact ⟨n, his, hn n le_rfl⟩
      rw [h_Ioi, Set.iUnion_prod_const]
      exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom
        (MeasureTheory.Filtration.Ioc_prod_mem_predictableRectangles _ i (seq n) hA)

lemma trimMeasure_T_eq_restrict (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas =
      ((ItoIntegralL2.timeMeasure.prod μ).trim
        𝓖.predictable_le_prod).restrict
        (Set.Ioc 0 T ×ˢ Set.univ) := by
  show ((timeMeasure_T T).prod μ).trim 𝓖.predictable_le_prod = _
  unfold timeMeasure_T
  rw [Measure.restrict_prod_eq_prod_univ,
      ← MeasureTheory.restrict_trim 𝓖.predictable_le_prod _
        (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓖) 0 T MeasurableSet.univ)]

lemma ae_fst_mem_Ioc_trimMeasure_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas), z.1 ∈ Set.Ioc 0 T := by
  rw [trimMeasure_T_eq_restrict (𝓖 := 𝓖)]
  exact (ae_restrict_mem (MeasureTheory.measurableSet_predictable_Ioc_prod
    (𝓕 := 𝓖) 0 T MeasurableSet.univ)).mono
    fun _ hz ↦ hz.1

variable (hB : IsPreBrownianReal B μ)

lemma memLp_uncurry_trim_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖) :
    MemLp (Function.uncurry ⇑V) 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
  rw [trimMeasure_T_eq_restrict (𝓖 := 𝓖)]
  exact (FilteredItoL2.memLp_uncurry_trim (F := 𝓖) hBmeas V).restrict _

noncomputable def simpleProcessL2_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ 𝓖) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) :=
  (memLp_uncurry_trim_T (𝓖 := 𝓖) T hBmeas V).toLp (Function.uncurry ⇑V)

def TBoundedSP (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Submodule ℝ (SimpleProcess ℝ 𝓖) where
  carrier := { V | ∀ p ∈ V.value.support, p.2 ≤ T }
  add_mem' {V W} hV hW p hp := by
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
    · exact hV p h
    · exact hW p h
  zero_mem' p hp := absurd hp (by simp)
  smul_mem' c V hV p hp := hV p (Finsupp.support_smul hp)

lemma uncurry_eq_zero_of_lt {T : ℝ≥0} {hBmeas : ∀ t, Measurable (B t)}
    (V : TBoundedSP (𝓖 := 𝓖) T hBmeas) {t : ℝ≥0} (ht : T < t) (ω : Ω) :
    Function.uncurry ⇑V.val (t, ω) = 0 := by
  show ⇑V.val t ω = 0
  rw [SimpleProcess.apply_eq]
  have ht0 : t ≠ ⊥ := by
    intro h
    rw [h, NNReal.bot_eq_zero] at ht
    exact absurd ht (by simp)
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ V.val.valueBot ω) t = 0 :=
    Set.indicator_of_notMem (by simpa using ht0) _
  rw [hbot, zero_add, Finsupp.sum]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  refine Set.indicator_of_notMem ?_ _
  simp only [Set.mem_Ioc, not_and, not_le]
  intro _
  exact lt_of_le_of_lt (V.property p hp) ht

private lemma eLpNorm_uncurry_trim_T_eq_trim (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := 𝓖) T hBmeas) :
    eLpNorm (Function.uncurry ⇑V.val) 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)
      = eLpNorm (Function.uncurry ⇑V.val) 2
          ((ItoIntegralL2.timeMeasure.prod μ).trim
            𝓖.predictable_le_prod) := by
  have hS_pred : MeasurableSet[𝓖.predictable] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓖) 0 T MeasurableSet.univ
  have hnull : ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓖.predictable_le_prod)
      ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) = 0 := by
    have hbot_meas : MeasurableSet[𝓖.predictable] ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) :=
      MeasureTheory.measurableSet_predictable_singleton_bot_prod
        (𝓕 := 𝓖) (s := (Set.univ : Set Ω)) MeasurableSet.univ
    rw [MeasureTheory.trim_measurableSet_eq 𝓖.predictable_le_prod hbot_meas,
        Measure.prod_prod, ItoIntegralL2.timeMeasure_singleton, zero_mul]
  have hae : {z : ℝ≥0 × Ω | z.1 ≠ 0} ∈ MeasureTheory.ae
      ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓖.predictable_le_prod) := by
    rw [show {z : ℝ≥0 × Ω | z.1 ≠ 0} = ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω))ᶜ by
          ext ⟨t, ω⟩; simp]
    exact compl_mem_ae_iff.mpr hnull
  have h_ae_eq : (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ⇑V.val)
      =ᵐ[((ItoIntegralL2.timeMeasure.prod μ).trim 𝓖.predictable_le_prod)]
        Function.uncurry ⇑V.val := by
    filter_upwards [hae] with z hz
    by_cases htT : z.1 ≤ T
    · rw [Set.indicator_of_mem]
      refine ⟨⟨?_, htT⟩, Set.mem_univ _⟩
      exact pos_iff_ne_zero.mpr hz
    · push Not at htT
      rw [Set.indicator_of_notMem]
      · exact (uncurry_eq_zero_of_lt (𝓖 := 𝓖) V htT z.2).symm
      · intro ⟨⟨_, hle⟩, _⟩
        exact absurd hle (not_le.mpr htT)
  calc eLpNorm (Function.uncurry ⇑V.val) 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)
      = eLpNorm (Function.uncurry ⇑V.val) 2
          (((ItoIntegralL2.timeMeasure.prod μ).trim 𝓖.predictable_le_prod).restrict
            (Set.Ioc 0 T ×ˢ Set.univ)) := by rw [trimMeasure_T_eq_restrict (𝓖 := 𝓖)]
    _ = eLpNorm ((Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ⇑V.val)) 2
          ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓖.predictable_le_prod) :=
        (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hS_pred.nullMeasurableSet).symm
    _ = eLpNorm (Function.uncurry ⇑V.val) 2
          ((ItoIntegralL2.timeMeasure.prod μ).trim 𝓖.predictable_le_prod) :=
        MeasureTheory.eLpNorm_congr_ae h_ae_eq

lemma simpleProcessL2_T_norm_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := 𝓖) T hBmeas) :
    ‖simpleProcessL2_T (𝓖 := 𝓖) (μ := μ) T hBmeas V.val‖
      = ‖FilteredItoL2.simpleProcessL2 (F := 𝓖) (μ := μ) hBmeas V.val‖ := by
  have h := eLpNorm_uncurry_trim_T_eq_trim (𝓖 := 𝓖) (μ := μ) T hBmeas V
  unfold simpleProcessL2_T FilteredItoL2.simpleProcessL2
  rw [Lp.norm_toLp, Lp.norm_toLp, h]

noncomputable def simpleAssembly_T (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    TBoundedSP (𝓖 := 𝓖) T hBmeas →ₗ[ℝ] Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) where
  toFun V := simpleProcessL2_T (𝓖 := 𝓖) T hBmeas V.val
  map_add' V W := by
    show simpleProcessL2_T (𝓖 := 𝓖) T hBmeas ((V + W).val) = _
    rw [Submodule.coe_add, simpleProcessL2_T, simpleProcessL2_T, simpleProcessL2_T,
        ← MemLp.toLp_add (memLp_uncurry_trim_T (𝓖 := 𝓖) T hBmeas V.val)
          (memLp_uncurry_trim_T (𝓖 := 𝓖) T hBmeas W.val)]
    congr 1
    exact FilteredItoL2.uncurry_coe_add (F := 𝓖) hBmeas V.val W.val
  map_smul' c V := by
    show simpleProcessL2_T (𝓖 := 𝓖) T hBmeas ((c • V).val) = _
    rw [Submodule.coe_smul, simpleProcessL2_T, simpleProcessL2_T, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_trim_T (𝓖 := 𝓖) T hBmeas V.val)]
    congr 1
    exact FilteredItoL2.uncurry_coe_smul (F := 𝓖) hBmeas c V.val

noncomputable def itoAssembly_T [IsFilteredPreBrownian B 𝓖 μ] (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    TBoundedSP (𝓖 := 𝓖) T hBmeas →ₗ[ℝ] Lp ℝ 2 μ :=
  (FilteredItoL2.itoAssembly (F := 𝓖) hB hBmeas).comp (TBoundedSP (𝓖 := 𝓖) T hBmeas).subtype

theorem assembly_isometry_T [IsFilteredPreBrownian B 𝓖 μ] (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (V : TBoundedSP (𝓖 := 𝓖) T hBmeas) :
    ‖itoAssembly_T (𝓖 := 𝓖) hB T hBmeas V‖ = ‖simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas V‖ := by
  show ‖FilteredItoL2.itoAssembly (F := 𝓖) hB hBmeas V.val‖
      = ‖simpleProcessL2_T (𝓖 := 𝓖) (μ := μ) T hBmeas V.val‖
  rw [simpleProcessL2_T_norm_eq (𝓖 := 𝓖) T hBmeas V]
  exact FilteredItoL2.assembly_isometry (F := 𝓖) hB hBmeas V.val

instance (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    IsFiniteMeasure (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
  unfold trimMeasure_T
  infer_instance

lemma setIntegral_eq_zero_of_orthogonal_pred (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    {g : ℝ≥0 × Ω → ℝ}
    (hg_int : Integrable g (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
    (h_orth : ∀ R ∈ predictableRect (𝓖 := 𝓖) (mΩ := mΩ) hBmeas,
      ∫ z in R, g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0)
    (s : Set (ℝ≥0 × Ω))
    (hs : MeasurableSet[𝓖.predictable] s) :
    ∫ z in s, g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0 := by
  have h_total : ∫ z, g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0 := by
    by_cases hT : 0 < T
    · -- `T > 0`: split ∫ univ into ∫_S + ∫_Sᶜ; both vanish.
      have hR : Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) ∈ predictableRect (𝓖 := 𝓖) (mΩ := mΩ) hBmeas :=
        Or.inr ⟨0, T, hT, Set.univ, MeasurableSet.univ, rfl⟩
      have hS_pred : MeasurableSet[𝓖.predictable] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓖) 0 T MeasurableSet.univ
      have hSc_null :
          (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))ᶜ = 0 := by
        rw [trimMeasure_T_eq_restrict (𝓖 := 𝓖),
            Measure.restrict_apply (MeasurableSet.compl hS_pred),
            Set.compl_inter_self]
        exact measure_empty
      have h_int_Sc : ∫ z in (Set.Ioc 0 T ×ˢ Set.univ)ᶜ, g z
          ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0 :=
        setIntegral_measure_zero g hSc_null
      have h_int_S := h_orth _ hR
      have h_split := integral_add_compl
        (μ := trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) (f := g) hS_pred hg_int
      linarith
    · -- `T = 0`: trim_T is the zero measure.
      push Not at hT
      have hT0 : T = 0 := le_antisymm hT bot_le
      have h_zero : trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas = 0 := by
        subst hT0
        unfold trimMeasure_T timeMeasure_T
        rw [Set.Ioc_self, Measure.restrict_empty, Measure.zero_prod,
            MeasureTheory.zero_trim]
      let gf : ℝ≥0 × Ω → ℝ := (g : ℝ≥0 × Ω → ℝ)
      show ∫ z, gf z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0
      rw [h_zero]
      exact integral_zero_measure gf
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ ↦ ∫ z in s, g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0)
    (h_eq := (generateFrom_predictableRect (𝓖 := 𝓖) hBmeas).symm)
    (h_inter := isPiSystem_predictableRect (𝓖 := 𝓖) hBmeas)
    (empty := setIntegral_empty)
    (basic := fun R hR ↦ h_orth R hR)
    (compl := ?_) (iUnion := ?_) s hs
  · -- Complement: `∫ g = ∫_S g + ∫_Sᶜ g`; total is zero, S piece is zero, so Sᶜ piece is zero.
    intro S hS hPS
    have h_split := integral_add_compl
      (μ := trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) (f := g) hS hg_int
    linarith
  · -- Disjoint countable union.
    intro f hf hfm hf_zero
    rw [integral_iUnion hfm hf hg_int.integrableOn]
    simp [hf_zero]

noncomputable def iocSP_T {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[𝓖 a] F) :
    TBoundedSP (𝓖 := 𝓖) T hBmeas :=
  ⟨(ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ), fun p hp ↦ by
    have h_I_eq : (ElementaryPredictableSet.IocProd a b hF).I = {(a, b)} := by
      show (if a ≤ b then ({(a, b)} : Finset _) else ∅) = _
      rw [if_pos hab]
    have h_in_I : p ∈ (ElementaryPredictableSet.IocProd a b hF).I := by
      by_contra hp_not
      apply Finsupp.mem_support_iff.mp hp
      show ((ElementaryPredictableSet.IocProd a b hF).indicator 1).value p = 0
      simp [ElementaryPredictableSet.indicator, Finsupp.onFinset_apply, hp_not]
    rw [h_I_eq, Finset.mem_singleton] at h_in_I
    rcases h_in_I with rfl
    exact hbT⟩

lemma uncurry_iocSP_T_eq {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[𝓖 a] F) :
    Function.uncurry ⇑(iocSP_T (𝓖 := 𝓖) hBmeas hab hbT hF : TBoundedSP (𝓖 := 𝓖) T hBmeas).val
      = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) := by
  funext ⟨t, ω⟩
  change ⇑((ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ)) t ω
      = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) (t, ω)
  rw [ElementaryPredictableSet.coe_indicator,
      ElementaryPredictableSet.coe_IocProd a b hF]
  rfl

private lemma inner_simpleAssembly_T_iocSP_T {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[𝓖 a] F)
    (g : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    ⟪simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas (iocSP_T (𝓖 := 𝓖) hBmeas hab hbT hF), g⟫_ℝ
      = ∫ z in Set.Ioc a b ×ˢ F, g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓖.predictable
  rw [L2.inner_def]
  have h_coe := MemLp.coeFn_toLp
    (memLp_uncurry_trim_T (𝓖 := 𝓖) (μ := μ) T hBmeas
      (iocSP_T (𝓖 := 𝓖) hBmeas hab hbT hF : TBoundedSP (𝓖 := 𝓖) T hBmeas).val)
  have h_uncurry_eq := uncurry_iocSP_T_eq (𝓖 := 𝓖) hBmeas hab hbT hF
  have h_ae_eq : ∀ᵐ z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas),
      (⟪(simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas (iocSP_T (𝓖 := 𝓖) hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z,
        (g : ℝ≥0 × Ω → ℝ) z⟫_ℝ : ℝ)
        = (Set.Ioc a b ×ˢ F).indicator (fun z ↦ (g : ℝ≥0 × Ω → ℝ) z) z := by
    filter_upwards [h_coe] with z hz
    have hSA_eq :
        (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas (iocSP_T (𝓖 := 𝓖) hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z
          = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z := by
      calc (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas (iocSP_T (𝓖 := 𝓖) hBmeas hab hbT hF) : ℝ≥0 × Ω → ℝ) z
          = Function.uncurry ⇑(iocSP_T (𝓖 := 𝓖) hBmeas hab hbT hF : TBoundedSP (𝓖 := 𝓖) T hBmeas).val z := hz
        _ = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z := by rw [h_uncurry_eq]
    rw [hSA_eq]
    show (g : ℝ≥0 × Ω → ℝ) z * (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z
        = (Set.Ioc a b ×ˢ F).indicator (fun z ↦ (g : ℝ≥0 × Ω → ℝ) z) z
    by_cases hz_in : z ∈ Set.Ioc a b ×ˢ F
    · rw [Set.indicator_of_mem hz_in, Set.indicator_of_mem hz_in, mul_one]
    · rw [Set.indicator_of_notMem hz_in, Set.indicator_of_notMem hz_in, mul_zero]
  rw [integral_congr_ae h_ae_eq]
  exact integral_indicator
    (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓖) a b hF)

lemma setIntegral_eq_setIntegral_inter_supp {T : ℝ≥0}
    (hBmeas : ∀ t, Measurable (B t))
    (g : ℝ≥0 × Ω → ℝ) (R : Set (ℝ≥0 × Ω))
    (hR : MeasurableSet[𝓖.predictable] R) :
    ∫ z in R, g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) =
      ∫ z in R ∩ (Set.Ioc 0 T ×ˢ Set.univ), g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓖.predictable
  have hS_pred : MeasurableSet (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓖) 0 T MeasurableSet.univ
  have h1 : (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas).restrict R
      = (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas).restrict (R ∩ Set.Ioc 0 T ×ˢ Set.univ) := by
    rw [trimMeasure_T_eq_restrict (𝓖 := 𝓖),
        Measure.restrict_restrict hR,
        Measure.restrict_restrict (hR.inter hS_pred),
        Set.inter_assoc, Set.inter_self]
  show ∫ z, g z ∂((trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas).restrict R)
      = ∫ z, g z ∂((trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas).restrict (R ∩ Set.Ioc 0 T ×ˢ Set.univ))
  rw [h1]

theorem simpleAssembly_T_denseRange (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    DenseRange (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
  suffices h_orth_bot :
      (LinearMap.range (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas))ᗮ = ⊥ by
    rw [denseRange_iff_closure_range,
        ← LinearMap.coe_range (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas),
        ← Submodule.topologicalClosure_coe,
        Submodule.topologicalClosure_eq_top_iff.mpr h_orth_bot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g h_mem
  rw [Submodule.mem_orthogonal] at h_mem
  have h_orth : ∀ R ∈ predictableRect (𝓖 := 𝓖) (mΩ := mΩ) hBmeas,
      ∫ z in R, g z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0 := by
    intro R hR
    rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, _hab, F, hF, rfl⟩
    · -- Bot: ∫_{{0} × F₀} g = 0 because {0} × F₀ ⊆ {0} × univ ⊆ (Ioc 0 T × univ)ᶜ
      have h_R_pred : MeasurableSet[𝓖.predictable] ({(⊥ : ℝ≥0)} ×ˢ F₀) :=
        MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓖) hF₀
      rw [setIntegral_eq_setIntegral_inter_supp (𝓖 := 𝓖) hBmeas g _ h_R_pred]
      have h_empty : ({(⊥ : ℝ≥0)} ×ˢ F₀) ∩ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) = ∅ := by
        rw [Set.prod_inter_prod,
            show ({(⊥ : ℝ≥0)} ∩ Set.Ioc 0 T : Set ℝ≥0) = ∅ by
              ext x; simp,
            Set.empty_prod]
      rw [h_empty, setIntegral_empty]
    · -- Ioc a b × F: bridge to Ioc a (min b T) × F, then orthogonality or empty.
      have h_R_pred : MeasurableSet[𝓖.predictable] (Set.Ioc a b ×ˢ F) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓖) a b hF
      rw [setIntegral_eq_setIntegral_inter_supp (𝓖 := 𝓖) hBmeas g _ h_R_pred]
      have h_inter : (Set.Ioc a b ×ˢ F) ∩ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          = Set.Ioc (max a 0) (min b T) ×ˢ F := by
        ext ⟨t, ω⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, hω⟩, ⟨h3, h4⟩⟩
          exact ⟨⟨max_lt h1 h3, le_min h2 h4⟩, hω⟩
        · rintro ⟨⟨h1, h2⟩, hω⟩
          refine ⟨⟨⟨(le_max_left _ _).trans_lt h1, h2.trans (min_le_left _ _)⟩, hω⟩, ?_⟩
          exact ⟨(le_max_right _ _).trans_lt h1, h2.trans (min_le_right _ _)⟩
      rw [h_inter]
      have hmax : max a 0 = a := max_eq_left bot_le
      rw [hmax]
      by_cases hab' : a ≤ min b T
      · -- Build iocSP_T (𝓖 := 𝓖) at (a, min b T, F): T-bounded with b' = min b T ≤ T.
        have hbT' : min b T ≤ T := min_le_right _ _
        have h_set := inner_simpleAssembly_T_iocSP_T (𝓖 := 𝓖) (μ := μ) hBmeas hab' hbT' hF g
        have h_inner := h_mem _ ⟨iocSP_T (𝓖 := 𝓖) hBmeas hab' hbT' hF, rfl⟩
        rw [← h_set]
        exact h_inner
      · -- a > min b T: Ioc a (min b T) = ∅, so R_T = ∅.
        push Not at hab'
        rw [Set.Ioc_eq_empty (not_lt.mpr hab'.le), Set.empty_prod, setIntegral_empty]
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓖.predictable
  refine (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr ?_
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun _ _ _ ↦ ((Lp.memLp g).integrable one_le_two).integrableOn)
    (fun s hs _ ↦ setIntegral_eq_zero_of_orthogonal_pred (𝓖 := 𝓖) T hBmeas
      ((Lp.memLp g).integrable one_le_two) h_orth s hs)

noncomputable def itoIntegralCLM_T [IsFilteredPreBrownian B 𝓖 μ] (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  (itoAssembly_T (𝓖 := 𝓖) hB T hBmeas).extendOfNorm (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas)

theorem itoIntegralCLM_T_simpleAssembly_T [IsFilteredPreBrownian B 𝓖 μ] (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (V : TBoundedSP (𝓖 := 𝓖) T hBmeas) :
    itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas V)
      = FilteredItoL2.itoSimpleLp (F := 𝓖) hB hBmeas V.val := by
  rw [itoIntegralCLM_T, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas)
    ⟨1, fun W ↦ by rw [one_mul]; exact (assembly_isometry_T (𝓖 := 𝓖) hB T hBmeas W).le⟩]
  rfl

theorem itoIntegralCLM_T_norm [IsFilteredPreBrownian B 𝓖 μ] (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (f : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    ‖itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas f‖ = ‖f‖ := by
  rw [itoIntegralCLM_T]
  exact LinearMap.norm_extendOfNorm_eq_of_isometry
    (simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas) (assembly_isometry_T (𝓖 := 𝓖) hB T hBmeas) f


end SHEStochastic.FilteredItoCLM
