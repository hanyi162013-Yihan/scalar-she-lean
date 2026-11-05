/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The contraction/density extension follows ItoIntegralProcessGeneral.lean
in formal-mathfin, 3c41aee9bf2d9743f9e66b439f90d1635843d2d2. The terminal
map is our native finite-horizon isometry; the elementary martingales use
the supplied noise frozen after H, with no extra Brownian randomness.
-/
module

public import SHEStochastic.IndependentDriverSimple
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.FiniteScalarItoProcess
open MeasureTheory ProbabilityTheory FiniteScalarIto
open scoped NNReal ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : Coordinates F μ H ι)
local notation "ν" => inputMeasure F μ H

theorem clipped_measurable (i : ι) : ∀ t, Measurable (clipped P i t) :=
  fun t ↦ measurable_coordinate P i (min t H)

def simpleProcess (i : ι) (V : Simple F H) (t : ℝ≥0) : Ω → ℝ :=
  FilteredItoProcess.itoSimpleProcess (clipped_measurable P i) V.val t

def simpleLp (i : ι) (V : Simple F H) (t : ℝ≥0) : Lp ℝ 2 μ :=
  IndependentDriverSimple.itoSimpleProcessLp (clipped_measurable P i) V.val t

theorem simpleLp_ae (i : ι) (V : Simple F H) (t : ℝ≥0) :
    simpleLp P i V t =ᵐ[μ] simpleProcess P i V t :=
  (IndependentDriverSimple.memLp_itoSimpleProcess (clipped_measurable P i) V.val t).coeFn_toLp

theorem simpleLp_adapted (i : ι) (V : Simple F H) (t : ℝ≥0) :
    AEStronglyMeasurable[F t] (simpleLp P i V t : Ω → ℝ) μ :=
  ⟨simpleProcess P i V t,
    (IndependentDriverSimple.itoSimpleProcess_adaptedAt (μ := μ) (clipped_measurable P i) V.val t).stronglyMeasurable,
    simpleLp_ae P i V t⟩

theorem simple_martingale (i : ι) (V : Simple F H) :
    Martingale (fun t ω ↦ simpleProcess P i V t ω) F μ :=
  IndependentDriverSimple.itoSimpleProcess_isMartingale (clipped_measurable P i) V.val

theorem simple_terminal (i : ι) (V : Simple F H) (t : ℝ≥0) (hHt : H ≤ t) :
    simpleProcess P i V t = FiniteScalarIto.simpleValue P i V := by
  have he := FilteredItoProcess.itoSimpleProcess_eq_itoSimple (clipped_measurable P i)
    V.val (fun p hp ↦ (V.property p hp).trans hHt)
  change FilteredItoProcess.itoSimpleProcess (clipped_measurable P i) V.val t = _
  rw [he]
  funext ω
  change V.val.value.sum (fun p v ↦ v ω * (clipped P i p.2 ω - clipped P i p.1 ω)) =
    V.val.value.sum (fun p v ↦ v ω * (P.W i p.2 ω - P.W i p.1 ω))
  apply Finsupp.sum_congr
  intro p hp
  have hp1 : p.1 ≤ H := (V.val.le_of_mem_support_value p hp).trans (V.property p hp)
  simp only [clipped, min_eq_left (V.property p hp), min_eq_left hp1]

theorem simple_condExp (i : ι) (V : Simple F H) (t : ℝ≥0) :
    μ[FiniteScalarIto.simpleValue P i V | F t] =ᵐ[μ] simpleProcess P i V t := by
  have he := (simple_martingale P i V).2 t (max t H) (le_max_left t H)
  change μ[simpleProcess P i V (max t H) | F t] =ᵐ[μ] simpleProcess P i V t at he
  rw [simple_terminal P i V (max t H) (le_max_right t H)] at he
  exact he

theorem simple_norm_bound (i : ι) (V : Simple F H) (t : ℝ≥0) :
    ‖simpleLp P i V t‖ ≤ ‖embedding F μ H V‖ := by
  have hb : eLpNorm (simpleProcess P i V t) 2 μ ≤
      eLpNorm (FiniteScalarIto.simpleValue P i V) 2 μ := by
    calc
      _ = eLpNorm (μ[FiniteScalarIto.simpleValue P i V | F t]) 2 μ :=
        (eLpNorm_congr_ae (simple_condExp P i V t)).symm
      _ ≤ _ := eLpNorm_condExp_le_eLpNorm _ (by simp)
  have hn : ‖simpleLp P i V t‖ ≤ ‖FiniteScalarIto.simpleLp P i V‖ := by
    rw [simpleLp, IndependentDriverSimple.itoSimpleProcessLp, Lp.norm_toLp,
      FiniteScalarIto.simpleLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono (memLp_simpleValue P i V).ne hb
  exact hn.trans_eq (simpleLp_norm P i V)

def ambientPrefixLM (i : ι) (t : ℝ≥0) : Simple F H →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := simpleLp P i V t
  map_add' V U := by
    simp only [simpleLp, Submodule.coe_add, IndependentDriverSimple.itoSimpleProcessLp]
    rw [← MemLp.toLp_add
        (IndependentDriverSimple.memLp_itoSimpleProcess (clipped_measurable P i) V.val t)
        (IndependentDriverSimple.memLp_itoSimpleProcess (clipped_measurable P i) U.val t)]
    congr 1
    exact FilteredItoProcess.itoSimpleProcess_add (clipped_measurable P i) V.val U.val t
  map_smul' c V := by
    simp only [simpleLp, Submodule.coe_smul, IndependentDriverSimple.itoSimpleProcessLp,
      RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c
        (IndependentDriverSimple.memLp_itoSimpleProcess (clipped_measurable P i) V.val t)]
    congr 1
    exact FilteredItoProcess.itoSimpleProcess_smul (clipped_measurable P i) c V.val t

def prefixLM (i : ι) (t : ℝ≥0) : Simple F H →ₗ[ℝ] lpMeas ℝ ℝ (F t) 2 μ :=
  (ambientPrefixLM P i t).codRestrict _
    (fun V ↦ mem_lpMeas_iff_aestronglyMeasurable.mpr (simpleLp_adapted P i V t))

theorem prefixLM_bound (i : ι) (t : ℝ≥0) (V : Simple F H) :
    ‖prefixLM P i t V‖ ≤ ‖embedding F μ H V‖ := simple_norm_bound P i V t

/-- Extend into the closed adapted L2 subspace, so adaptation is retained
by the construction itself. -/
def prefixSubspaceCLM (i : ι) (t : ℝ≥0) : Lp ℝ 2 ν →L[ℝ] lpMeas ℝ ℝ (F t) 2 μ := by
  letI : Fact (F t ≤ ‹MeasurableSpace Ω›) := ⟨F.le t⟩
  exact (prefixLM P i t).extendOfNorm (embedding F μ H)

def prefixCLM (i : ι) (t : ℝ≥0) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (lpMeas ℝ ℝ (F t) 2 μ).subtypeL.comp (prefixSubspaceCLM P i t)

theorem prefixSubspaceCLM_simple (i : ι) (t : ℝ≥0) (V : Simple F H) :
    prefixSubspaceCLM P i t (embedding F μ H V) = prefixLM P i t V := by
  letI : Fact (F t ≤ ‹MeasurableSpace Ω›) := ⟨F.le t⟩
  rw [prefixSubspaceCLM, LinearMap.extendOfNorm_eq (embedding_dense F μ H)
    ⟨1, fun U ↦ by rw [one_mul]; exact prefixLM_bound P i t U⟩]

theorem prefixCLM_simple (i : ι) (t : ℝ≥0) (V : Simple F H) :
    prefixCLM P i t (embedding F μ H V) = simpleLp P i V t := by
  change (prefixSubspaceCLM P i t (embedding F μ H V) : Lp ℝ 2 μ) = _
  rw [prefixSubspaceCLM_simple]
  rfl

theorem prefixCLM_adapted (i : ι) (t : ℝ≥0) (v : Lp ℝ 2 ν) :
    AEStronglyMeasurable[F t] (prefixCLM P i t v : Ω → ℝ) μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mp (prefixSubspaceCLM P i t v).property

theorem simpleLp_terminal (i : ι) (V : Simple F H) :
    simpleLp P i V H = FiniteScalarIto.simpleLp P i V := by
  apply Lp.ext
  exact ((simpleLp_ae P i V H).trans
    (Filter.Eventually.of_forall (congrFun (simple_terminal P i V H le_rfl)))).trans
      (memLp_simpleValue P i V).coeFn_toLp.symm

theorem prefixCLM_terminal (i : ι) (v : Lp ℝ 2 ν) :
    prefixCLM P i H v = rawIsometry P i v := by
  exact congrFun (DenseRange.equalizer (embedding_dense F μ H)
    (prefixCLM P i H).continuous (rawIsometry P i).continuous
    (funext fun V ↦ by
      change prefixCLM P i H (embedding F μ H V) = rawIsometry P i (embedding F μ H V)
      rw [prefixCLM_simple, rawIsometry_simple, simpleLp_terminal])) v

/-- The adapted extension is the conditional expectation of this very
terminal integral, rather than an independently chosen version. -/
theorem prefixCLM_eq_condExpL2 (i : ι) (t : ℝ≥0) (v : Lp ℝ 2 ν) :
    prefixCLM P i t v = (condExpL2 ℝ ℝ (F.le t) (rawIsometry P i v) : Lp ℝ 2 μ) := by
  have hc : Continuous fun f : Lp ℝ 2 ν ↦
      (condExpL2 ℝ ℝ (F.le t) (rawIsometry P i f) : Lp ℝ 2 μ) :=
    (continuous_subtype_val.comp (condExpL2 ℝ ℝ (F.le t)).continuous).comp
      (rawIsometry P i).continuous
  refine congrFun (DenseRange.equalizer (embedding_dense F μ H)
    (prefixCLM P i t).continuous hc (funext fun V ↦ ?_)) v
  simp only [Function.comp_apply]
  rw [prefixCLM_simple, rawIsometry_simple]
  apply Lp.ext
  filter_upwards [simpleLp_ae P i V t,
    (memLp_simpleValue P i V).condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le t),
    simple_condExp P i V t] with ω h1 h2 h3
  change simpleLp P i V t ω = _ at h1
  rw [h1, ← h3]
  exact h2.symm

theorem prefixCLM_norm_le (i : ι) (t : ℝ≥0) (v : Lp ℝ 2 ν) :
    ‖prefixCLM P i t v‖ ≤ ‖v‖ := by
  have ha : (prefixCLM P i t v : Ω → ℝ) =ᵐ[μ]
      μ[(rawIsometry P i v : Ω → ℝ) | F t] := by
    rw [prefixCLM_eq_condExpL2]
    have h := (Lp.memLp (rawIsometry P i v)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (F.le t)
    rwa [Lp.toLp_coeFn] at h
  rw [← (rawIsometry P i).norm_map v, Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae ha]
  exact ENNReal.toReal_mono (Lp.memLp (rawIsometry P i v)).ne
    (eLpNorm_condExp_le_eLpNorm _ (by simp))

end SHEStochastic.FiniteScalarItoProcess
