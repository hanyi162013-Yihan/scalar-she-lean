module

public import SHEStochastic.FiniteCylindricalSimple
public import SHEStochastic.FiniteScalarItoTruncation
public import SHEStochastic.FilteredStoppedIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FiniteCylindricalIto
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

theorem sourceEquiv_ae (e : HilbertBasis ι ℝ C) (v : Lp C 2 ν) (i : ι) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    sourceEquiv e v i =ᵐ[ν] fun p ↦ innerSL ℝ (e i) (v p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [sourceEquiv_coordinate]
  exact (innerSL ℝ (e i)).coeFn_compLpL v

variable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

theorem rawIntegral_eq_prefix_of_band (q : ℝ≥0) (hq : q ≤ H) (f g : Lp C 2 ν)
    (hg : g =ᵐ[ν] (Set.Ioc 0 q ×ˢ (Set.univ : Set Ω)).indicator f) :
    rawIntegral P.toCoordinates e g = prefixCLM P e q f := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hc (i : ι) : sourceEquiv e g i = FiniteScalarItoProcess.trunc q (sourceEquiv e f i) := by
    apply Lp.ext
    filter_upwards [sourceEquiv_ae e g i, sourceEquiv_ae e f i,
      FiniteScalarItoProcess.trunc_ae q (sourceEquiv e f i), hg] with p hgc hfc htr hgp
    rw [hgc, htr]
    by_cases hp : p ∈ Set.Ioc 0 q ×ˢ (Set.univ : Set Ω)
    · rw [Set.indicator_of_mem hp, hfc, hgp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, hgp, Set.indicator_of_notMem hp, map_zero]
  let L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (lpMeas ℝ ℝ (F q) 2 μ).subtypeL.comp (condExpL2 ℝ ℝ (F.le q))
  have hs := L.hasSum (rawIntegral_hasSum P.toCoordinates e f)
  have he (i : ι) : FiniteScalarIto.rawIsometry P.toCoordinates i (sourceEquiv e g i) =
      L (FiniteScalarIto.rawIsometry P.toCoordinates i (sourceEquiv e f i)) := by
    rw [hc, FiniteScalarItoProcess.rawIsometry_trunc P i q hq,
      FiniteScalarItoProcess.prefixCLM_eq_condExpL2]
    rfl
  exact (rawIntegral_hasSum P.toCoordinates e g).unique (hs.congr_fun he)

omit P e in
theorem processTransport_stop_ae (q : ℝ≥0) (v : Process (E := C) F μ H) :
    processTransport (StoppedItoInputs.stop F μ H q v) =ᵐ[ν]
      (StoppedItoInputs.before q).indicator (processTransport v) := by
  have hstop := ((Lp.memLp v).indicator
    (StoppedItoInputs.before_measurable F q).nullMeasurableSet).coeFn_toLp
  have hle : ae ν ≤ ae ((energyMeasure μ H).trim (predictable_le_product F)) := by
    rw [FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)]
    exact le_rfl
  filter_upwards [processTransport_ae (StoppedItoInputs.stop F μ H q v),
    hstop.filter_mono hle, processTransport_ae v] with p hp hs hv
  rw [hp]
  change StoppedItoInputs.stop F μ H q v p = _ at hs
  rw [hs]
  by_cases h : p ∈ StoppedItoInputs.before (Ω := Ω) q
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; exact hv.symm
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

/-- Strict-before stopping agrees with the continuous integral process,
including all times after H, where the input and process are frozen. -/
theorem stopped_eq_prefix_min (q : ℝ≥0) (v : Process (E := C) F μ H) :
    (terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H q v) =
      prefixCLM P e (min q H) (processTransport v) := by
  change rawIntegral P.toCoordinates e (processTransport (StoppedItoInputs.stop F μ H q v)) = _
  apply rawIntegral_eq_prefix_of_band P e (min q H) (min_le_right q H)
  filter_upwards [processTransport_stop_ae q v,
    FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const),
    FilteredScalarIto.trim_ae_fst_ne (𝓖 := F) (μ := μ) H q
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with p hp hm hn
  rw [hp]
  have hi : p ∈ StoppedItoInputs.before (Ω := Ω) q ↔
      p ∈ Set.Ioc 0 (min q H) ×ˢ (Set.univ : Set Ω) := by
    constructor
    · intro h
      exact ⟨⟨hm.1, le_min (by exact_mod_cast (show (p.1 : ℝ) < (q : ℝ) from h).le) hm.2⟩,
        Set.mem_univ _⟩
    · intro h
      change (p.1 : ℝ) < (q : ℝ)
      exact_mod_cast lt_of_le_of_ne ((le_min_iff.mp h.1.2).1) hn
  by_cases h : p ∈ StoppedItoInputs.before (Ω := Ω) q
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hi.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' ↦ h (hi.mpr h'))]

end SHEStochastic.FiniteCylindricalIto
