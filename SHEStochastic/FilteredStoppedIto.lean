module

public import SHEStochastic.FilteredScalarIto
public import SHEStochastic.FilteredItoContinuousModification
public import SHE.StoppedItoInputs
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.FilteredScalarIto
open MeasureTheory Set ProbabilityTheory SHE.PredictableL2
open FilteredItoCLM FilteredItoProcessGeneral
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  [hFB : IsFilteredPreBrownian B 𝓖 μ]

omit hFB in
theorem processTransport_stop_ae (T q : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (v : Process (E := ℝ) 𝓖 μ T) :
    processTransport T hBmeas (SHE.StoppedItoInputs.stop 𝓖 μ T q v)
      =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas]
        (SHE.StoppedItoInputs.before q).indicator (processTransport T hBmeas v) := by
  have hstop := ((Lp.memLp v).indicator
    (SHE.StoppedItoInputs.before_measurable 𝓖 q).nullMeasurableSet).coeFn_toLp
  have hle : ae (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) ≤
      ae ((energyMeasure μ T).trim (predictable_le_product 𝓖)) := by
    rw [processMeasure_eq T hBmeas]
  filter_upwards [processTransport_ae T hBmeas (SHE.StoppedItoInputs.stop 𝓖 μ T q v),
    hstop.filter_mono hle, processTransport_ae T hBmeas v] with p hp hs hv
  change processTransport T hBmeas (SHE.StoppedItoInputs.stop 𝓖 μ T q v) p = _
  rw [hp]
  change SHE.StoppedItoInputs.stop 𝓖 μ T q v p = _ at hs
  rw [hs]
  by_cases h : p ∈ SHE.StoppedItoInputs.before (Ω := Ω) q
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact hv.symm
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

omit hFB in
theorem trim_ae_fst_ne (T q : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ p ∂trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas, p.1 ≠ q := by
  rw [ae_iff]
  simp only [not_not]
  change trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas {p | p.1 = q} = 0
  have hm : MeasurableSet[𝓖.predictable] {p : ℝ≥0 × Ω | p.1 = q} :=
    measurableSet_eq_fun (SHE.PredictableClock.time_measurable 𝓖) measurable_const
  unfold trimMeasure_T
  rw [trim_measurableSet_eq 𝓖.predictable_le_prod hm,
    show {p : ℝ≥0 × Ω | p.1 = q} = {q} ×ˢ (Set.univ : Set Ω) by ext; simp,
    Measure.prod_prod, MathFin.ItoIntegralCLM.timeMeasure_T,
    Measure.restrict_apply (measurableSet_singleton q)]
  have hz : MathFin.ItoIntegralL2.timeMeasure ({q} ∩ Ioc 0 T) = 0 :=
    measure_mono_null inter_subset_left (MathFin.ItoIntegralL2.timeMeasure_singleton q)
  rw [hz, zero_mul]

/-- The strict-before convention in the manuscript agrees with the
usual stopped scalar integral, since deterministic time points are null. -/
theorem stopped_eq_process (hB : IsPreBrownianReal B μ) (T q : ℝ≥0) (hq : q ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (v : Process (E := ℝ) 𝓖 μ T) :
    (terminalIto hB T hBmeas).integral (SHE.StoppedItoInputs.stop 𝓖 μ T q v) =
      itoProcessCLM (𝓖 := 𝓖) hB T q hBmeas (processTransport T hBmeas v) := by
  let f := processTransport T hBmeas v
  let g := processTransport T hBmeas (SHE.StoppedItoInputs.stop 𝓖 μ T q v)
  have hbefore : ∀ᵐ p ∂trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas,
      p.1 ≤ q → (f - g) p = 0 := by
    filter_upwards [processTransport_stop_ae T q hBmeas v, trim_ae_fst_ne T q hBmeas,
      Lp.coeFn_sub f g] with p hp hn hs hle
    rw [hs, Pi.sub_apply]
    change f p - g p = 0
    rw [show g p = (SHE.StoppedItoInputs.before q).indicator f p from hp,
      Set.indicator_of_mem, sub_self]
    change (p.1 : ℝ) < (q : ℝ)
    exact_mod_cast lt_of_le_of_ne hle hn
  have hzero := itoProcessCLM_eq_zero_of_vanishes_before (𝓖 := 𝓖)
    hB T q hq hBmeas (f - g) hbefore
  rw [map_sub, sub_eq_zero] at hzero
  change itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas g = _
  rw [itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after (𝓖 := 𝓖) hB T q hq hBmeas g
    (processTransport_stopped T q hBmeas _ (SHE.StoppedItoInputs.stop_stopped 𝓖 μ T q v))]
  exact hzero.symm

omit hFB in
theorem stop_eq_self_after_horizon (T q : ℝ≥0) (hTq : T < q)
    (hBmeas : ∀ t, Measurable (B t)) (v : Process (E := ℝ) 𝓖 μ T) :
    SHE.StoppedItoInputs.stop 𝓖 μ T q v = v := by
  apply (processTransport T hBmeas).injective
  apply Lp.ext
  filter_upwards [processTransport_stop_ae T q hBmeas v,
    ae_fst_mem_Ioc_trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] with p hp ht
  rw [hp, Set.indicator_of_mem]
  change (p.1 : ℝ) < (q : ℝ)
  exact_mod_cast ht.2.trans_lt hTq

theorem stopped_eq_process_min (hB : IsPreBrownianReal B μ) (T q : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (v : Process (E := ℝ) 𝓖 μ T) :
    (terminalIto hB T hBmeas).integral (SHE.StoppedItoInputs.stop 𝓖 μ T q v) =
      itoProcessCLM (𝓖 := 𝓖) hB T (min q T) hBmeas (processTransport T hBmeas v) := by
  by_cases hq : q ≤ T
  · simpa only [min_eq_left hq] using stopped_eq_process hB T q hq hBmeas v
  · have hTq := lt_of_not_ge hq
    rw [stop_eq_self_after_horizon T q hTq hBmeas v, min_eq_right hTq.le,
      itoProcessCLM_terminal_eq (𝓖 := 𝓖)]
    rfl

/-- An actual continuous predictable version of all deterministic stops
of the SAME scalar integral, obtained from the public continuous-modification
construction and the paper's null-complete-filtration lemma. -/
theorem exists_continuous_stopped_version (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ B t ω))
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets 𝓖 μ)
    (v : Process (E := ℝ) 𝓖 μ T) :
    ∃ Y : ℝ≥0 × Ω → ℝ, StronglyMeasurable[𝓖.predictable] Y ∧
      (∀ ω, Continuous (fun t ↦ Y (t, ω))) ∧
      (∀ q : ℝ≥0, (fun ω ↦ Y (q, ω)) =ᵐ[μ]
        (terminalIto hB T hBmeas).integral (SHE.StoppedItoInputs.stop 𝓖 μ T q v)) := by
  classical
  obtain ⟨X, hX, hC⟩ :=
    FilteredItoContinuousModification.exists_continuous_modification_itoProcess (𝓖 := 𝓖)
      hB T hBmeas hBcont (processTransport T hBmeas v)
  let Z (t : ℝ≥0) (ω : Ω) := X (min t T) ω
  have hZc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Z t ω) := by
    filter_upwards [hC] with ω hω
    exact hω.comp_continuous (continuous_id.min continuous_const)
      (fun t ↦ ⟨zero_le, min_le_right t T⟩)
  have hZrep (q : ℝ≥0) : Z q =ᵐ[μ]
      (terminalIto hB T hBmeas).integral (SHE.StoppedItoInputs.stop 𝓖 μ T q v) := by
    rw [stopped_eq_process_min hB T q hBmeas v]
    exact hX (min q T) (min_le_right q T)
  let U (t : ℝ≥0) (ω : Ω) := if Continuous (fun s ↦ Z s ω) then Z t ω else 0
  have hUc (ω : Ω) : Continuous (fun t ↦ U t ω) := by
    by_cases hω : Continuous (fun s ↦ Z s ω)
    · simpa only [U, if_pos hω] using hω
    · simpa only [U, if_neg hω] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ)))
  have hUrep (q : ℝ≥0) : U q =ᵐ[μ]
      (terminalIto hB T hBmeas).integral (SHE.StoppedItoInputs.stop 𝓖 μ T q v) := by
    apply Filter.EventuallyEq.trans _ (hZrep q)
    filter_upwards [hZc] with ω hω
    exact if_pos hω
  have hUa (q : ℝ≥0) : ∃ A : Ω → ℝ, StronglyMeasurable[𝓖 q] A ∧ U q =ᵐ[μ] A := by
    obtain ⟨A, hA, he⟩ := SHE.StoppedItoInputs.stopped_integral_adapted 𝓖 μ T
      (terminalIto hB T hBmeas) q v
    exact ⟨A, hA, (hUrep q).trans he⟩
  exact ⟨Function.uncurry U,
    SHE.NullCompleteFiltration.predictable_of_continuous_versions 𝓖 μ hnull U hUa hUc,
    hUc, hUrep⟩

end SHEStochastic.FilteredScalarIto
