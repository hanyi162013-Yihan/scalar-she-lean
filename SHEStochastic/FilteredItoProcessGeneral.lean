/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Adapted from formal-mathfin, 3c41aee9bf2d9743f9e66b439f90d1635843d2d2,
ItoIntegralProcessGeneral.lean. Density extends the elementary integral to
an L2-continuous martingale in the full supplied Brownian filtration.
-/
module

public import MathFin.Foundations.ItoIntegralProcessGeneral
public import SHEStochastic.FilteredItoProcessMartingale
public import SHEStochastic.FilteredItoCLM

@[expose] public section
namespace SHEStochastic.FilteredItoProcessGeneral
open MeasureTheory ProbabilityTheory
open FilteredItoL2 FilteredItoCLM FilteredItoProcess
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
  (hB : IsPreBrownianReal B μ) [hFB : IsFilteredPreBrownian B 𝓖 μ]
include hB hFB

theorem itoSimpleProcessLp_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ 𝓖) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    ‖itoSimpleProcessLp (𝓖 := 𝓖) hB hBmeas V t‖ ≤ ‖simpleProcessL2_T (𝓖 := 𝓖) (μ := μ) T hBmeas V‖ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hnorm_eq : ‖simpleProcessL2_T (𝓖 := 𝓖) (μ := μ) T hBmeas V‖ = ‖itoSimpleLp (F := 𝓖) hB hBmeas V‖ :=
    (assembly_isometry_T (𝓖 := 𝓖) hB T hBmeas ⟨V, hVT⟩).symm
  rw [hnorm_eq]
  have hT'eq : itoSimpleProcess (𝓖 := 𝓖) hBmeas V (max t T) = itoSimple (F := 𝓖) hBmeas V :=
    itoSimpleProcess_eq_itoSimple (𝓖 := 𝓖) hBmeas V fun p hp ↦ (hVT p hp).trans (le_max_right t T)
  have hcond : (μ[fun ω ↦ itoSimpleProcess (𝓖 := 𝓖) hBmeas V (max t T) ω | 𝓖 t])
      =ᵐ[μ] fun ω ↦ itoSimpleProcess (𝓖 := 𝓖) hBmeas V t ω :=
    (itoSimpleProcess_isMartingale (𝓖 := 𝓖) hB hBmeas V).2 t (max t T) (le_max_left t T)
  simp only [hT'eq] at hcond
  simp only [itoSimpleProcessLp, itoSimpleLp, Lp.norm_toLp]
  refine ENNReal.toReal_mono (memLp_itoSimple (F := 𝓖) hB hBmeas V).ne ?_
  calc eLpNorm (itoSimpleProcess (𝓖 := 𝓖) hBmeas V t) 2 μ
      = eLpNorm (μ[itoSimple (F := 𝓖) hBmeas V | 𝓖 t]) 2 μ :=
        (eLpNorm_congr_ae hcond).symm
    _ ≤ eLpNorm (itoSimple (F := 𝓖) hBmeas V) 2 μ := eLpNorm_condExp_le_eLpNorm _ (by simp)

noncomputable def itoProcessLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    TBoundedSP (𝓖 := 𝓖) T hBmeas →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := itoSimpleProcessLp (𝓖 := 𝓖) hB hBmeas V.val t
  map_add' V W := by
    show itoSimpleProcessLp (𝓖 := 𝓖) hB hBmeas ((V + W).val) t = _
    rw [Submodule.coe_add, itoSimpleProcessLp, itoSimpleProcessLp, itoSimpleProcessLp,
        ← MemLp.toLp_add (memLp_itoSimpleProcess (𝓖 := 𝓖) hB hBmeas V.val t)
          (memLp_itoSimpleProcess (𝓖 := 𝓖) hB hBmeas W.val t)]
    congr 1
    exact itoSimpleProcess_add (𝓖 := 𝓖) hBmeas V.val W.val t
  map_smul' c V := by
    show itoSimpleProcessLp (𝓖 := 𝓖) hB hBmeas ((c • V).val) t = _
    rw [Submodule.coe_smul, itoSimpleProcessLp, itoSimpleProcessLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_itoSimpleProcess (𝓖 := 𝓖) hB hBmeas V.val t)]
    congr 1
    exact itoSimpleProcess_smul (𝓖 := 𝓖) hBmeas c V.val t

noncomputable def itoProcessCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  (itoProcessLM (𝓖 := 𝓖) hB T t hBmeas).extendOfNorm (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas)

theorem itoProcessCLM_simpleAssembly_T (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP (𝓖 := 𝓖) T hBmeas) :
    itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas V)
      = itoSimpleProcessLp (𝓖 := 𝓖) hB hBmeas V.val t := by
  rw [itoProcessCLM, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas)
    ⟨1, fun W ↦ by rw [one_mul]; exact itoSimpleProcessLp_norm_le (𝓖 := 𝓖) hB T t hBmeas W.val W.property⟩]
  rfl

@[simp] theorem itoProcessCLM_zero_time (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    itoProcessCLM (𝓖 := 𝓖) hB T 0 hBmeas φ = 0 := by
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas)
    (itoProcessCLM (𝓖 := 𝓖) hB T 0 hBmeas).continuous
    (continuous_const (y := (0 : Lp ℝ 2 μ))) (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T (𝓖 := 𝓖), itoSimpleProcessLp]
  refine Lp.ext (((memLp_itoSimpleProcess (𝓖 := 𝓖) hB hBmeas V.val 0).coeFn_toLp).trans ?_)
  rw [itoSimpleProcess_zero_time (𝓖 := 𝓖)]
  exact (Lp.coeFn_zero ℝ 2 μ).symm

omit [IsProbabilityMeasure μ] in

theorem condExp_itoSimple_eq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ 𝓖) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    μ[itoSimple (F := 𝓖) hBmeas V | 𝓖 t]
      =ᵐ[μ] fun ω ↦ itoSimpleProcess (𝓖 := 𝓖) hBmeas V t ω := by
  have hT'eq : itoSimpleProcess (𝓖 := 𝓖) hBmeas V (max t T) = itoSimple (F := 𝓖) hBmeas V :=
    itoSimpleProcess_eq_itoSimple (𝓖 := 𝓖) hBmeas V fun p hp ↦ (hVT p hp).trans (le_max_right t T)
  simpa only [hT'eq] using (itoSimpleProcess_isMartingale (𝓖 := 𝓖) hB hBmeas V).2 t (max t T) (le_max_left t T)

theorem itoProcessCLM_eq_condExpL2 (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas φ
      = (condExpL2 ℝ ℝ (𝓖.le t)
          (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ) : Lp ℝ 2 μ) := by
  have hcont_R : Continuous fun ψ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) ↦
      (condExpL2 ℝ ℝ (𝓖.le t)
        (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas ψ) : Lp ℝ 2 μ) :=
    (continuous_subtype_val.comp (condExpL2 ℝ ℝ (𝓖.le t)).continuous).comp
      (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas).continuous
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas)
    (itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas).continuous hcont_R (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply]
  rw [itoProcessCLM_simpleAssembly_T (𝓖 := 𝓖), itoIntegralCLM_T_simpleAssembly_T (𝓖 := 𝓖)]
  refine Lp.ext ?_
  simp only [itoSimpleProcessLp, itoSimpleLp]
  filter_upwards [(memLp_itoSimpleProcess (𝓖 := 𝓖) hB hBmeas V.val t).coeFn_toLp,
    (memLp_itoSimple (F := 𝓖) hB hBmeas V.val).condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓖.le t),
    condExp_itoSimple_eq (𝓖 := 𝓖) hB T t hBmeas V.val V.property] with ω hω1 hω2 hω3
  rw [hω1, ← hω3, hω2]

theorem itoProcessCLM_aeStronglyMeasurable (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    AEStronglyMeasurable[𝓖 t]
      (itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas φ : Ω → ℝ) μ := by
  rw [itoProcessCLM_eq_condExpL2 (𝓖 := 𝓖)]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (condExpL2 ℝ ℝ (𝓖.le t) (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ)).2

theorem itoIntegralProcessGen_isMartingale (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessCLM (𝓖 := 𝓖) hB T j hBmeas φ : Ω → ℝ) | 𝓖 i]
      =ᵐ[μ] (itoProcessCLM (𝓖 := 𝓖) hB T i hBmeas φ : Ω → ℝ) := by
  have hbridge : ∀ k : ℝ≥0,
      ((condExpL2 ℝ ℝ (𝓖.le k)
          (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ)
        =ᵐ[μ] μ[(itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ : Ω → ℝ) | 𝓖 k] := by
    intro k
    have h := (Lp.memLp (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (𝓖.le k)
    rwa [Lp.toLp_coeFn] at h
  rw [itoProcessCLM_eq_condExpL2 (𝓖 := 𝓖), itoProcessCLM_eq_condExpL2 (𝓖 := 𝓖)]
  calc μ[((condExpL2 ℝ ℝ (𝓖.le j)
            (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ) | 𝓖 i]
      =ᵐ[μ] μ[μ[(itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ : Ω → ℝ) | 𝓖 j]
              | 𝓖 i] := condExp_congr_ae (hbridge j)
    _ =ᵐ[μ] μ[(itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ : Ω → ℝ) | 𝓖 i] :=
        condExp_condExp_of_le (𝓖.mono hij) (𝓖.le j)
    _ =ᵐ[μ] ((condExpL2 ℝ ℝ (𝓖.le i)
              (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ) := (hbridge i).symm

theorem itoProcessCLM_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    ‖itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas φ‖ ≤ ‖φ‖ := by
  have hae : (itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas φ : Ω → ℝ)
      =ᵐ[μ] μ[(itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ : Ω → ℝ) | 𝓖 t] := by
    rw [itoProcessCLM_eq_condExpL2 (𝓖 := 𝓖)]
    have h := (Lp.memLp (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (𝓖.le t)
    rwa [Lp.toLp_coeFn] at h
  rw [Lp.norm_def, ← itoIntegralCLM_T_norm (𝓖 := 𝓖) hB T hBmeas φ, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.memLp (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ)).ne ?_
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_condExp_le_eLpNorm _ (by simp)

theorem itoProcessCLM_terminal_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    itoProcessCLM (𝓖 := 𝓖) hB T T hBmeas φ = itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ :=
  congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas)
    (itoProcessCLM (𝓖 := 𝓖) hB T T hBmeas).continuous (itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas).continuous
    (funext fun V ↦ by
      simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T (𝓖 := 𝓖),
        itoIntegralCLM_T_simpleAssembly_T (𝓖 := 𝓖), itoSimpleProcessLp, itoSimpleLp,
        itoSimpleProcess_eq_itoSimple (𝓖 := 𝓖) hBmeas V.val (fun p hp ↦ V.property p hp)])) φ

theorem itoProcessCLM_norm_terminal (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    ‖itoProcessCLM (𝓖 := 𝓖) hB T T hBmeas φ‖ = ‖φ‖ := by
  rw [itoProcessCLM_terminal_eq (𝓖 := 𝓖) hB T hBmeas φ, itoIntegralCLM_T_norm (𝓖 := 𝓖) hB T hBmeas φ]

theorem integral_itoIntegralCLM_T (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    ∫ ω, itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ ω ∂μ = 0 := by
  have hmart := itoIntegralProcessGen_isMartingale (𝓖 := 𝓖) hB T hBmeas φ (i := 0) (j := T) zero_le
  rw [itoProcessCLM_zero_time (𝓖 := 𝓖) hB T hBmeas φ] at hmart
  rw [← itoProcessCLM_terminal_eq (𝓖 := 𝓖) hB T hBmeas φ,
    ← integral_condExp (𝓖.le 0), integral_congr_ae hmart]
  simp

theorem itoIntegralProcessGen_l2_continuous (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    Continuous (fun t ↦ itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas φ) := by
  obtain ⟨g, hg_range, hg_lim⟩ := mem_closure_iff_seq_limit.mp
    ((simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas).closure_range.ge (Set.mem_univ φ))
  choose V hV using hg_range
  have hcont_n : ∀ n, Continuous (fun t ↦ itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas (g n)) := fun n ↦ by
    simp only [← hV n, itoProcessCLM_simpleAssembly_T (𝓖 := 𝓖)]
    exact itoSimpleProcessLp_l2_continuous (𝓖 := 𝓖) hB hBmeas (V n).val
  have huniform : TendstoUniformly (fun n t ↦ itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas (g n))
      (fun t ↦ itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas φ) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hnorm_lim : Filter.Tendsto (fun n ↦ ‖φ - g n‖) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := φ)).sub hg_lim
      simpa using this.norm
    filter_upwards [hnorm_lim.eventually (eventually_lt_nhds hε)] with n hn t
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (itoProcessCLM_norm_le (𝓖 := 𝓖) hB T t hBmeas (φ - g n)) hn
  exact huniform.continuous (Filter.Eventually.of_forall hcont_n).frequently


end SHEStochastic.FilteredItoProcessGeneral
