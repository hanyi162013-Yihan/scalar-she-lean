module

public import SHEStochastic.FilteredSimpleLocality

/-! Extend the reused elementary past-factor identity by predictable-simple
density to the native finite-horizon scalar isometries. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FiniteScalarIto
open MeasureTheory ProbabilityTheory FilteredSimpleLocality
open MathFin (afterFactor abs_afterFactor_le mulBddCLM coeFn_mulBddCLM)
open scoped NNReal ENNReal Topology
variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local notation "ν" => inputMeasure F μ H

variable {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))

theorem smulAdaptedCLM_ae (a : ℝ≥0) (Z : Ω → ℝ) (hZm : Measurable[F a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (f : Lp ℝ 2 ν) :
    smulAdaptedCLM (F := F) (μ := μ) H a Z hZm C hZb f =ᵐ[ν]
      fun p ↦ afterFactor a Z p * f p :=
  coeFn_mulBddCLM _ (measurable_afterFactor hZm) (abs_afterFactor_le hZb) f

theorem afterStep_embedding (a : ℝ≥0) (Z : Ω → ℝ) (hZm : Measurable[F a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : Simple F H) :
    embedding F μ H (afterStepSP H a hBmeas Z hZm C hZb V) =
      smulAdaptedCLM (F := F) (μ := μ) H a Z hZm C hZb (embedding F μ H V) := by
  apply Lp.ext
  filter_upwards [
    (FilteredItoCLM.memLp_uncurry_trim_T (𝓖 := F) (μ := μ) H hBmeas
      (afterStepSP H a hBmeas Z hZm C hZb V).val).coeFn_toLp,
    smulAdaptedCLM_ae a Z hZm C hZb (embedding F μ H V),
    (FilteredItoCLM.memLp_uncurry_trim_T (𝓖 := F) (μ := μ) H hBmeas V.val).coeFn_toLp,
    FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H hBmeas]
      with p h1 h2 h3 hp
  change embedding F μ H (afterStepSP H a hBmeas Z hZm C hZb V) p = _ at h1
  change embedding F μ H V p = _ at h3
  rw [h1, h2, h3]
  exact coe_afterStepSP H a hBmeas Z hZm C hZb V (ne_of_gt hp.1) p.2

variable (P : Coordinates F μ H ι)

/-- A bounded random factor measurable in the supplied past passes through
the native scalar integral, with both inputs switched on after that past. -/
theorem rawIsometry_after_factor (i : ι) (a : ℝ≥0) (Z : Ω → ℝ)
    (hZm : Measurable[F a] Z) (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (f : Lp ℝ 2 ν) :
    rawIsometry P i
      (smulAdaptedCLM (F := F) H a Z hZm C hZb f) =
      mulBddCLM μ (hZm.mono (F.le a) le_rfl) hZb
        (rawIsometry P i (smulAdaptedCLM (F := F) H a
          (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le) f)) := by
  let bm := measurable_coordinate P i
  let S := smulAdaptedCLM (F := F) (μ := μ) H a Z hZm C hZb
  let R := smulAdaptedCLM (F := F) (μ := μ) H a
    (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le)
  let L := mulBddCLM μ (hZm.mono (F.le a) le_rfl) hZb
  refine congrFun (DenseRange.equalizer (embedding_dense F μ H)
    ((rawIsometry P i).continuous.comp S.continuous)
    (L.continuous.comp ((rawIsometry P i).continuous.comp R.continuous))
    (funext fun V ↦ ?_)) f
  simp only [Function.comp_apply]
  change rawIsometry P i (S (embedding F μ H V)) = L (rawIsometry P i (R (embedding F μ H V)))
  rw [← afterStep_embedding bm a Z hZm C hZb V,
    ← afterStep_embedding bm a (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le) V,
    rawIsometry_simple, rawIsometry_simple]
  apply Lp.ext
  let U := afterStepSP H a bm Z hZm C hZb V
  let U₁ := afterStepSP H a bm (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le) V
  filter_upwards [(memLp_simpleValue P i U).coeFn_toLp,
    coeFn_mulBddCLM μ (hZm.mono (F.le a) le_rfl) hZb (simpleLp P i U₁),
    (memLp_simpleValue P i U₁).coeFn_toLp] with ω h1 h2 h3
  change simpleLp P i U ω = _ at h1
  change simpleLp P i U₁ ω = _ at h3
  rw [h1, h2, h3]
  exact itoSimple_afterStepSP_smul H a bm Z hZm C hZb V ω

theorem rawIsometry_after_factor_ae (i : ι) (a : ℝ≥0) (Z : Ω → ℝ)
    (hZm : Measurable[F a] Z) (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (f : Lp ℝ 2 ν) :
    rawIsometry P i
      (smulAdaptedCLM (F := F) H a Z hZm C hZb f) =ᵐ[μ]
      fun ω ↦ Z ω * rawIsometry P i
        (smulAdaptedCLM (F := F) H a
          (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le) f) ω := by
  rw [rawIsometry_after_factor P i a Z hZm C hZb]
  exact coeFn_mulBddCLM _ _ _ _

end SHEStochastic.FiniteScalarIto
