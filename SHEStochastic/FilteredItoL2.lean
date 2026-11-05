/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Generalized from formal-mathfin at 3c41aee9bf2d9743f9e66b439f90d1635843d2d2,
ItoIntegralL2.lean. The simple-process isometry now uses any filtration in
which B is Brownian. Deterministic time-measure lemmas are reused unchanged.
-/
module

public import MathFin.Foundations.ItoIntegralL2
public import SHEStochastic.FilteredBrownianCore

@[expose] public section

namespace SHEStochastic.FilteredItoL2

open MeasureTheory ProbabilityTheory
open MathFin.ItoIntegralL2 (timeMeasure timeMeasure_Ioc timeMeasure_Ioc_inter
  elemIntegrand ae_fst_ne_zero_prod lp_two_norm_sq)
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}


noncomputable def itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) : Ω → ℝ :=
  fun ω ↦ V.value.sum fun p v ↦ v ω * (B p.2 ω - B p.1 ω)

lemma itoSimple_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (ω : Ω) :
    itoSimple (F := F) hBmeas V ω
      = V.value.sum fun p v ↦ v ω * (B p.2 ω - B p.1 ω) :=
  rfl

variable [IsProbabilityMeasure μ]

theorem memLp_itoSimple [IsFilteredPreBrownian B F μ] (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    MemLp (itoSimple (F := F) hBmeas V) 2 μ := by
  rw [show itoSimple (F := F) hBmeas V
        = fun ω ↦ ∑ p ∈ V.value.support, V.value p ω * (B p.2 ω - B p.1 ω)
      from funext fun ω ↦ by rw [itoSimple_apply (F := F)]; rfl]
  refine memLp_finsetSum V.value.support (fun p hp ↦ ?_)
  refine FilteredBrownianCore.memLp_adapted_mul_increment hB hBmeas (V.le_of_mem_support_value p hp)
    (V.measurable_value p) ?_
  exact MemLp.of_bound
    ((V.measurable_value p).mono (F.le p.1) le_rfl).aestronglyMeasurable
    V.valueBound (ae_of_all _ (V.value_le_valueBound p))

noncomputable def itoSimpleLp [IsFilteredPreBrownian B F μ] (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) : Lp ℝ 2 μ :=
  (memLp_itoSimple (F := F) hB hBmeas V).toLp _

theorem itoSimple_sq_integral [IsFilteredPreBrownian B F μ] (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    ∫ ω, (itoSimple (F := F) hBmeas V ω) ^ 2 ∂μ
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  set a : (ℝ≥0 × ℝ≥0) → Ω → ℝ := fun p ω ↦ V.value p ω * (B p.2 ω - B p.1 ω)
  have ha_L2 : ∀ p ∈ V.value.support, MemLp (a p) 2 μ := fun p hp ↦
    FilteredBrownianCore.memLp_adapted_mul_increment hB hBmeas (V.le_of_mem_support_value p hp)
      (V.measurable_value p)
      (MemLp.of_bound
        ((V.measurable_value p).mono (F.le p.1) le_rfl).aestronglyMeasurable
        V.valueBound (ae_of_all _ (V.value_le_valueBound p)))
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun ω ↦ a p ω * a q ω) μ :=
    fun p hp q hq ↦ (ha_L2 p hp).integrable_mul (ha_L2 q hq)
  calc ∫ ω, (itoSimple (F := F) hBmeas V ω) ^ 2 ∂μ
      = ∫ ω, ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        show itoSimple (F := F) hBmeas V ω ^ 2
          = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω
        rw [show itoSimple (F := F) hBmeas V ω = ∑ p ∈ V.value.support, a p ω from by
              rw [itoSimple_apply (F := F)]; rfl, sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, ∫ ω, a p ω * a q ω ∂μ := by
        rw [integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hint p hp q hq)]
        exact Finset.sum_congr rfl fun p hp ↦
          integral_finsetSum _ (fun q hq ↦ hint p hp q hq)
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
        refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun q hq ↦ ?_
        exact FilteredBrownianCore.rect_increment_pairing hB hBmeas
          (V.measurable_value p)
          (V.measurable_value q)
          (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p ω)
          (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound q ω)
          (V.le_of_mem_support_value p hp) (V.le_of_mem_support_value q hq)

theorem itoSimpleLp_norm_sq [IsFilteredPreBrownian B F μ] (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    ‖(itoSimpleLp (F := F) hB hBmeas V : Lp ℝ 2 μ)‖ ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  rw [lp_two_norm_sq, ← itoSimple_sq_integral (F := F) hB hBmeas V]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_itoSimple (F := F) hB hBmeas V).coeFn_toLp] with ω hω
  rw [show (itoSimpleLp (F := F) hB hBmeas V : Ω → ℝ) ω = itoSimple (F := F) hBmeas V ω from hω]

noncomputable def rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (p : ℝ≥0 × ℝ≥0) :
    ℝ≥0 × Ω → ℝ :=
  elemIntegrand p.1 p.2 (V.value p)

lemma rectTerm_eq_indicator (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (p : ℝ≥0 × ℝ≥0) :
    rectTerm (F := F) hBmeas V p
      = (Set.Ioc p.1 p.2 ×ˢ (Set.univ : Set Ω)).indicator (fun z ↦ V.value p z.2) := by
  funext z
  rw [rectTerm, elemIntegrand, Set.indicator_apply, Set.indicator_apply]
  simp only [Set.mem_prod, Set.mem_univ, and_true]
  split_ifs <;> simp

lemma memLp_rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (p : ℝ≥0 × ℝ≥0) :
    MemLp (rectTerm (F := F) hBmeas V p) 2 (timeMeasure.prod μ) := by
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc p.1 p.2)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, timeMeasure_Ioc];
        exact ENNReal.ofReal_lt_top⟩
  rw [rectTerm_eq_indicator (F := F),
      memLp_indicator_iff_restrict
        (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet,
      ← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : Measurable (fun z : ℝ≥0 × Ω ↦ V.value p z.2) :=
    ((V.measurable_value p).mono (F.le p.1) le_rfl).comp measurable_snd
  exact MemLp.of_bound hmeas.aestronglyMeasurable V.valueBound
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact V.value_le_valueBound p z.2)

lemma uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero {m : MeasurableSpace (ℝ≥0 × Ω)}
    {ν : @Measure (ℝ≥0 × Ω) m} (hν : ∀ᵐ z ∂ν, z.1 ≠ 0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    Function.uncurry ⇑V =ᵐ[ν] fun z ↦ ∑ p ∈ V.value.support, rectTerm (F := F) hBmeas V p z := by
  filter_upwards [hν] with z hz
  show ⇑V z.1 z.2 = _
  rw [SimpleProcess.apply_eq, Set.indicator_of_notMem (by simpa using hz), zero_add, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [rectTerm, elemIntegrand, Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> simp

lemma uncurry_ae_eq_sum_rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    Function.uncurry ⇑V
      =ᵐ[timeMeasure.prod μ] fun z ↦ ∑ p ∈ V.value.support, rectTerm (F := F) hBmeas V p z :=
  uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero (F := F) (ae_fst_ne_zero_prod μ) hBmeas V

lemma memLp_uncurry_prod (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    MemLp (Function.uncurry ⇑V) 2 (timeMeasure.prod μ) :=
  (memLp_congr_ae (uncurry_ae_eq_sum_rectTerm (F := F) hBmeas V)).mpr
    (memLp_finsetSum _ fun p _ ↦ memLp_rectTerm (F := F) hBmeas V p)

lemma memLp_uncurry_trim (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    MemLp (Function.uncurry ⇑V) 2
      ((timeMeasure.prod μ).trim F.predictable_le_prod) := by
  change eLpNorm _ _ _ < ∞
  rw [eLpNorm_trim _ V.isStronglyPredictable]
  exact memLp_uncurry_prod (F := F) hBmeas V

noncomputable def simpleProcessL2 (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim F.predictable_le_prod) :=
  (memLp_uncurry_trim (F := F) hBmeas V).toLp (Function.uncurry ⇑V)

lemma integral_rectTerm_mul (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (p q : ℝ≥0 × ℝ≥0) :
    ∫ z, rectTerm (F := F) hBmeas V p z * rectTerm (F := F) hBmeas V q z ∂(timeMeasure.prod μ)
      = (∫ ω, V.value p ω * V.value q ω ∂μ)
          * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  have hfun : (fun z : ℝ≥0 × Ω ↦ rectTerm (F := F) hBmeas V p z * rectTerm (F := F) hBmeas V q z)
      = fun z ↦ ((Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) z.1
                    * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) z.1)
                  * (V.value p z.2 * V.value q z.2) := by
    funext z; simp only [rectTerm, elemIntegrand]; ring
  rw [hfun, integral_prod_mul
        (fun i ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
          * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i)
        (fun ω ↦ V.value p ω * V.value q ω), mul_comm]
  congr 1
  have hpt : ∀ i : ℝ≥0, (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
        * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i
        = (Set.Ioc p.1 p.2 ∩ Set.Ioc q.1 q.2).indicator (1 : ℝ≥0 → ℝ) i := by
    intro i; rw [Set.inter_indicator_one]; rfl
  simp_rw [hpt]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc),
      Measure.real_def, timeMeasure_Ioc_inter, ENNReal.toReal_ofReal', max_comm]

theorem simpleProcessL2_norm_sq (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    ‖simpleProcessL2 (F := F) (μ := μ) hBmeas V‖ ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  have hStepA : ‖simpleProcessL2 (F := F) (μ := μ) hBmeas V‖ ^ 2
      = ∫ z, (Function.uncurry ⇑V z) ^ 2 ∂(timeMeasure.prod μ) := by
    rw [lp_two_norm_sq (simpleProcessL2 (F := F) (μ := μ) hBmeas V)]
    have hco : (fun z ↦ (simpleProcessL2 (F := F) (μ := μ) hBmeas V z) ^ 2)
        =ᵐ[(timeMeasure.prod μ).trim F.predictable_le_prod]
          fun z ↦ (Function.uncurry ⇑V z) ^ 2 := by
      filter_upwards [(memLp_uncurry_trim (F := F) hBmeas V).coeFn_toLp] with z hz
      rw [show (simpleProcessL2 (F := F) (μ := μ) hBmeas V) z = Function.uncurry ⇑V z from hz]
    rw [integral_congr_ae hco]
    simp only [pow_two]
    have hsm2 : StronglyMeasurable[F.predictable]
        (fun z ↦ Function.uncurry ⇑V z * Function.uncurry ⇑V z) :=
      V.isStronglyPredictable.mul V.isStronglyPredictable
    exact (integral_trim F.predictable_le_prod hsm2).symm
  rw [hStepA]
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun z ↦ rectTerm (F := F) hBmeas V p z * rectTerm (F := F) hBmeas V q z) (timeMeasure.prod μ) :=
    fun p _ q _ ↦ (memLp_rectTerm (F := F) hBmeas V p).integrable_mul (memLp_rectTerm (F := F) hBmeas V q)
  have hsq : ∀ᵐ z ∂(timeMeasure.prod μ), (Function.uncurry ⇑V z) ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          rectTerm (F := F) hBmeas V p z * rectTerm (F := F) hBmeas V q z := by
    filter_upwards [uncurry_ae_eq_sum_rectTerm (F := F) hBmeas V] with z hz
    rw [hz, sq, Finset.sum_mul_sum]
  rw [integral_congr_ae hsq,
      integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hint p hp q hq)]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [integral_finsetSum _ fun q hq ↦ hint p hp q hq]
  exact Finset.sum_congr rfl fun q _ ↦ integral_rectTerm_mul (F := F) hBmeas V p q

lemma itoSimple_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ F) :
    itoSimple (F := F) hBmeas (V + W) = itoSimple (F := F) hBmeas V + itoSimple (F := F) hBmeas W := by
  funext ω
  simp only [itoSimple, Pi.add_apply, show (V + W).value = V.value + W.value from rfl]
  exact Finsupp.sum_add_index' (fun p ↦ by simp) (fun p v w ↦ by simp [add_mul])

lemma itoSimple_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ F) :
    itoSimple (F := F) hBmeas (c • V) = c • itoSimple (F := F) hBmeas V := by
  funext ω
  simp only [itoSimple, Pi.smul_apply, smul_eq_mul,
    show (c • V).value = c • V.value from rfl]
  rw [Finsupp.sum_smul_index' (fun p ↦ by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun p _ ↦ by simp [mul_assoc]

noncomputable def itoAssembly [IsFilteredPreBrownian B F μ] (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ F →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := itoSimpleLp (F := F) hB hBmeas V
  map_add' V W := by
    rw [itoSimpleLp, itoSimpleLp, itoSimpleLp,
        ← MemLp.toLp_add (memLp_itoSimple (F := F) hB hBmeas V) (memLp_itoSimple (F := F) hB hBmeas W)]
    congr 1
    exact itoSimple_add (F := F) hBmeas V W
  map_smul' c V := by
    rw [itoSimpleLp, itoSimpleLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_itoSimple (F := F) hB hBmeas V)]
    congr 1
    exact itoSimple_smul (F := F) hBmeas c V

lemma uncurry_coe_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ F) :
    Function.uncurry ⇑(V + W) = Function.uncurry ⇑V + Function.uncurry ⇑W := by
  rw [SimpleProcess.coe_add]; rfl

lemma uncurry_coe_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ F) :
    Function.uncurry ⇑(c • V) = c • Function.uncurry ⇑V := by
  rw [SimpleProcess.coe_smul]; rfl

noncomputable def simpleAssembly (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ F
      →ₗ[ℝ] Lp ℝ 2 ((timeMeasure.prod μ).trim F.predictable_le_prod) where
  toFun V := simpleProcessL2 (F := F) (μ := μ) hBmeas V
  map_add' V W := by
    rw [simpleProcessL2, simpleProcessL2, simpleProcessL2,
        ← MemLp.toLp_add (memLp_uncurry_trim (F := F) hBmeas V) (memLp_uncurry_trim (F := F) hBmeas W)]
    congr 1
    exact uncurry_coe_add (F := F) hBmeas V W
  map_smul' c V := by
    rw [simpleProcessL2, simpleProcessL2, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_trim (F := F) hBmeas V)]
    congr 1
    exact uncurry_coe_smul (F := F) hBmeas c V

theorem assembly_isometry [IsFilteredPreBrownian B F μ] (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) :
    ‖itoAssembly (F := F) (μ := μ) hB hBmeas V‖ = ‖simpleAssembly (F := F) (μ := μ) hBmeas V‖ := by
  have hsq : ‖itoAssembly (F := F) (μ := μ) hB hBmeas V‖ ^ 2 = ‖simpleAssembly (F := F) (μ := μ) hBmeas V‖ ^ 2 := by
    show ‖(itoSimpleLp (F := F) hB hBmeas V : Lp ℝ 2 μ)‖ ^ 2 = ‖simpleProcessL2 (F := F) (μ := μ) hBmeas V‖ ^ 2
    rw [itoSimpleLp_norm_sq (F := F) hB hBmeas V, simpleProcessL2_norm_sq (F := F) hBmeas V]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq


end SHEStochastic.FilteredItoL2
