module

public import SHEStochastic.PredictableMultiplier
public import SHEStochastic.WeightedPrimitiveSums
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.PredictableLeftSteps
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def step (w : ℝ≥0 → Ω → ℝ) (n : ℕ) (p : ℝ≥0 × Ω) : ℝ :=
  WeightedPrimitiveSums.step H (fun t ↦ w t p.2) n p.1

theorem predictable (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w) (n : ℕ) :
    StronglyMeasurable[F.predictable] (step (H := H) w n) := by
  unfold step WeightedPrimitiveSums.step
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  convert PredictableSteps.step_stronglyMeasurable F (unifPart H n k) (unifPart H n (k + 1))
    (hw (unifPart H n k)) using 1
  funext p
  simp only [PredictableSteps.step, Set.indicator_apply, Set.mem_Ioc]

/-- The disjoint cells preserve the bound globally, including outside
the physical horizon and the empty partition. -/
theorem bound (w : ℝ≥0 → Ω → ℝ) (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B)
    (n : ℕ) (p : ℝ≥0 × Ω) : |step (H := H) w n p| ≤ B := by
  by_cases hp : p.1 ∈ Set.Ioc 0 H
  · exact MathFin.ItoIntegralRiemannBridge.abs_sum_indicator_unifPart_le H n hp hB (fun t ↦ hwb t p.2)
  · have hz : step (H := H) w n p = 0 := by
      unfold step WeightedPrimitiveSums.step
      apply Finset.sum_eq_zero
      intro k hk
      apply Set.indicator_of_notMem
      intro hm
      apply hp
      exact ⟨lt_of_le_of_lt zero_le hm.1,
        hm.2.trans (MathFin.ItoIntegralBrownian.unifPart_le_T (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))⟩
    rw [hz, abs_zero]
    exact hB

/-- Continuous adapted weights are approximated in the original
predictable measure, without completing or changing the filtration. -/
theorem tendsto_ae_trim (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H)) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F),
      Filter.Tendsto (fun n ↦ step (H := H) w n p) Filter.atTop (𝓝 (w p.1 p.2)) := by
  have hs : ∀ᵐ r ∂timeMeasure H, r ∈ Set.Ioc 0 H := by
    rw [timeMeasure_eq]
    exact ae_restrict_mem measurableSet_Ioc
  have hprod : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H,
      Filter.Tendsto (fun n ↦ step (H := H) w n p) Filter.atTop (𝓝 (w p.1 p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
      Measure.quasiMeasurePreserving_snd.ae hc] with p hs hp
    exact MathFin.ItoIntegralRiemannBridge.tendsto_sum_indicator_unifPart H hs
      (hp p.1 ⟨zero_le, hs.2⟩)
  have hwp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ w p.1 p.2) := by
    simpa only [Function.uncurry_def] using hp
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hm : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω |
      Filter.Tendsto (fun n ↦ step (H := H) w n p) Filter.atTop (𝓝 (w p.1 p.2))} :=
    measurableSet_tendsto_fun (fun n ↦ (predictable w hw n).measurable) hwp.measurable
  rw [ae_iff]
  exact (trim_measurableSet_eq (μ := energyMeasure μ H) (predictable_le_product F) hm.compl).trans hprod

section WeightedInput
variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]

def input (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) : Process (E := C) F μ H :=
  PredictableMultiplier.process u (step (H := H) w n) (predictable w hw n) B (bound w B hB hwb n)

/-- Dominated convergence acts on the existing predictable L² space:
left-step weights times an arbitrary L² row converge to that row times
the original continuous weight. -/
theorem tendsto_input (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ)
    (hw : StronglyAdapted F w) (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    Filter.Tendsto (input u w hw B hB hwb) Filter.atTop
      (𝓝 (PredictableMultiplier.process u (Function.uncurry w) hp B (fun p ↦ hwb p.1 p.2))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let g := PredictableMultiplier.process u (Function.uncurry w) hp B (fun p ↦ hwb p.1 p.2)
  apply LpDominatedLimit.tendsto (B • u) g (input u w hw B hB hwb)
  · intro n
    exact PredictableMultiplier.norm_process_le u _ _ B hB _
  · exact PredictableMultiplier.norm_process_le u _ hp B hB _
  · have hf : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ∀ n,
        input u w hw B hB hwb n p = step (H := H) w n p • u p :=
      ae_all_iff.mpr (fun n ↦ PredictableMultiplier.process_ae_trim u _ _ B _)
    filter_upwards [hf, PredictableMultiplier.process_ae_trim u _ hp B (fun p ↦ hwb p.1 p.2),
      tendsto_ae_trim w hw hp hc] with p hfω hgω hsω
    have heq : (fun n ↦ input u w hw B hB hwb n p) =
        (fun n ↦ step (H := H) w n p • u p) := funext hfω
    change Filter.Tendsto (fun n ↦ input u w hw B hB hwb n p) Filter.atTop (𝓝 (g p))
    rw [heq, hgω]
    exact hsω.smul_const (u p)

end WeightedInput
end SHEStochastic.PredictableLeftSteps
