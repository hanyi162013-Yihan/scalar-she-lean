/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Reused through ContinuousMartingaleExtension from formal-mathfin, 3c41aee9bf2d9743f9e66b439f90d1635843d2d2,
ItoIntegralProcessContinuousModification.lean and the elementary continuity
lemma in ItoIntegralProcessLocalMartingale.lean. Only verified weak maximal
inequalities are used, with the given full Brownian filtration.
-/
module

public import SHEStochastic.ContinuousMartingaleExtension

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SHEStochastic.FilteredItoProcess
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}

theorem itoSimpleProcess_pathContinuous (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ 𝓖) (ω : Ω) :
    Continuous fun t : ℝ≥0 ↦ itoSimpleProcess hBmeas V t ω := by
  simp_rw [fun t ↦ itoSimpleProcess_apply hBmeas V t ω, Finsupp.sum]
  refine continuous_finsetSum _ fun p _ ↦ ?_
  refine continuous_const.mul (Continuous.sub ?_ ?_)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)
end SHEStochastic.FilteredItoProcess

namespace SHEStochastic.FilteredItoContinuousModification
open FilteredItoL2 FilteredItoCLM FilteredItoProcess FilteredItoProcessGeneral
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
  (hB : IsPreBrownianReal B μ) [hFB : IsFilteredPreBrownian B 𝓖 μ]

def continuousModel (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) :
    ContinuousMartingaleExtension.Model
      (Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
      (TBoundedSP (𝓖 := 𝓖) T hBmeas) 𝓖 μ T where
  embedding := simpleAssembly_T T hBmeas
  dense := simpleAssembly_T_denseRange T hBmeas
  process :=
    { toFun := fun V ↦ itoSimpleProcess hBmeas V.val
      map_add' := fun V U ↦ by
        funext t ω
        exact congrFun (itoSimpleProcess_add hBmeas V.val U.val t) ω
      map_smul' := fun c V ↦ by
        funext t ω
        exact congrFun (itoSimpleProcess_smul hBmeas c V.val t) ω }
  martingale := fun V ↦ itoSimpleProcess_isMartingale hB hBmeas V.val
  continuous := fun V ω ↦ itoSimpleProcess_pathContinuous hBmeas hBcont V.val ω
  atTime := fun t ↦ itoProcessCLM hB T t hBmeas
  representative V t := by
    rw [itoProcessCLM_simpleAssembly_T]
    exact (memLp_itoSimpleProcess hB hBmeas V.val t).coeFn_toLp
  terminal_bound V := by rw [itoProcessCLM_norm_terminal]

theorem exists_continuous_modification_itoProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, t ≤ T → X t =ᵐ[μ] itoProcessCLM (𝓖 := 𝓖) hB T t hBmeas φ) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T)) :=
  (continuousModel (𝓖 := 𝓖) hB T hBmeas hBcont).exists_continuous_modification φ

end SHEStochastic.FilteredItoContinuousModification
