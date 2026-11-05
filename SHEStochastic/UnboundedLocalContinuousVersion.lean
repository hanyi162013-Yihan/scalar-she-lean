module

public import SHEStochastic.UnboundedLocalizedHeatRows
public import SHEStochastic.NativeFieldLocalization
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import SHEStochastic.PhysicalHeatParameterSection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.UnboundedLocalContinuousVersion
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 AddCircle Filter
open HeatParameterCover HeatParameterCoordinates
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

def observation (n : ℕ) : Parameter → Ω → ℝ :=
  UnboundedHeatContinuity.observation F (UnboundedL2Localization.state U n)
    (UnboundedL2Localization.predictable F U hU n) hG hβ hβ1 μ H
    (UnboundedL2Localization.history_bound U μ H n) P e

theorem observation_adapted (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (n : ℕ) (p : Parameter) :
    StronglyMeasurable[F (time H p)] (observation F U hU hG hβ hβ1 μ H P e n p) := by
  let u := UnboundedLocalizedHeatRows.row F U hU hG hβ hβ1 μ H n (time H p)
    (time_le_horizon H p) (time_le_one H p) (center p)
  have hu : StoppedItoInputs.stop F μ H (time H p) u = u :=
    UnboundedHeatFamily.input_stop F _ _ hG hβ hβ1 μ H (time H p)
      (time_le_horizon H p) (time_le_one H p) (center p) _
  obtain ⟨Z, hZ, he⟩ := StoppedItoInputs.stopped_integral_adapted F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (time H p) u
  rw [hu] at he
  exact NullCompleteFiltration.stronglyMeasurable_congr F μ hnull (time H p) hZ he

/-- A version locally equal to the cutoff convolutions is adapted,
even when its original definition selected a cutoff using the whole
future horizon. Eventual equality gives a measurable limiting version
in the past sigma algebra, and null completeness identifies the two. -/
theorem adapted_of_cutoffs (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (Y : Parameter → Ω → ℝ)
    (he : ∀ n p, ∀ᵐ ω ∂μ, (time H p : WithTop ℝ≥0) <
      ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) n ω →
        Y p ω = observation F U hU hG hβ hβ1 μ H P e n p ω) (p : Parameter) :
    StronglyMeasurable[F (time H p)] (Y p) := by
  exact NativeFieldLocalization.adapted F μ hnull (time H p)
    (ContinuousNormExit.exit (fun t ω ↦ U (t,ω)))
    (ContinuousNormExit.tendsto_top (fun t ω ↦ U (t,ω)) hc)
    (fun n ↦ observation F U hU hG hβ hβ1 μ H P e n p)
    (fun n ↦ observation_adapted F U hU hG hβ hβ1 μ H P e hnull n p) (Y p) (fun n ↦ he n p)

/-- Assemble a continuous local stochastic convolution for any
predictable continuous L2 state, with no deterministic state bound.
The parameter clock is the already constructed interval [0,min(H,1)].
The field is consistent with every native cutoff convolution before
its exit, has finite compact bounds and vanishes uniformly initially. -/
theorem exists_version (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Y : Parameter → Ω → ℝ, (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (time H p)] (Y p)) ∧
      (∀ ω, Continuous (fun p ↦ Y p ω)) ∧
      (∀ n p, ∀ᵐ ω ∂μ, (time H p : WithTop ℝ≥0) <
        ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) n ω →
          Y p ω = observation F U hU hG hβ hβ1 μ H P e n p ω) ∧
      ∀ᵐ ω ∂μ, (∀ p, Y (zeroTime p) ω = 0) ∧
        (∃ M : ℝ, 0 ≤ M ∧ ∀ p, |Y p ω| ≤ M) ∧
          ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
            ∀ p : Parameter, |p.val 0| < δ → |Y p ω| < ε := by
  have hv (n : ℕ) : ∃ Z : Parameter → Ω → ℝ, (∀ p, Measurable (Z p)) ∧
      (∀ p, Z p=ᵐ[μ] observation F U hU hG hβ hβ1 μ H P e n p) ∧
      (∀ ω, Continuous (fun p ↦ Z p ω)) ∧ ∀ᵐ ω ∂μ, ∀ p, Z (zeroTime p) ω=0 := by
    obtain ⟨Z,hm,he,hc,hz⟩ := UnboundedHeatInitialVersion.exists_uniformly_vanishing_version F
      (UnboundedL2Localization.state U n) (UnboundedL2Localization.predictable F U hU n)
      hG hβ hβ1 μ H (UnboundedL2Localization.history_bound U μ H n) P e
    exact ⟨Z,hm,he,hc,hz.mono fun ω hω ↦ hω.1⟩
  let τ := ContinuousNormExit.exit (fun t ω ↦ U (t,ω))
  have hescape : ∀ ω, ∃ n, (H:WithTop ℝ≥0)<τ n ω := by
    intro ω
    have ht := ContinuousNormExit.tendsto_top (fun t ω ↦ U (t,ω)) hc ω
    rw [WithTop.tendsto_nhds_top_iff] at ht
    exact (ht H).exists
  have hcompat (n m : ℕ) (p : Parameter) : ∀ᵐ ω ∂μ,
      (time H p:WithTop ℝ≥0)<τ n ω → (time H p:WithTop ℝ≥0)<τ m ω →
        observation F U hU hG hβ hβ1 μ H P e n p ω=observation F U hU hG hβ hβ1 μ H P e m p ω := by
    have hh := UnboundedLocalizedHeatRows.native_eq_before F U hU hG hβ hβ1 μ H hc
      (min n m) n m (time H p) (by exact_mod_cast Nat.min_le_left n m)
      (by exact_mod_cast Nat.min_le_right n m) (time_le_horizon H p) (time_le_one H p) (center p) P e hnull
    filter_upwards [hh] with ω he hpn hpm
    apply he
    rcases le_total n m with h | h
    · simpa only [min_eq_left h] using hpn.le
    · simpa only [min_eq_right h] using hpm.le
  obtain ⟨Y,hYm,hYc,hYe,hz⟩ := LocalizedFieldAssembly.exists_of_modifications H τ hescape μ
    (time H) (time_le_horizon H) (observation F U hU hG hβ hβ1 μ H P e) zeroTime hv hcompat (fun n ↦ by
      simpa only [Set.compl_setOf, not_le] using
        ((F.le H) _ (UnboundedL2Localization.exit_stopping F U hU hc n H)).compl)
  refine ⟨Y,hYm,adapted_of_cutoffs F U hU hG hβ hβ1 μ H P e hc hnull Y hYe,hYc,hYe,?_⟩
  filter_upwards [hz] with ω hω
  exact ⟨hω,HeatParameterInitialBound.bounded (fun p ↦ Y p ω) (hYc ω),
    fun _ hε ↦ HeatParameterInitialBound.uniformly_small (fun p ↦ Y p ω) (hYc ω) hω hε⟩

/-- The constructed local field has strongly measurable physical paths
in both L2 and L-infinity and its L-infinity remainder tends to zero
initially. These are conclusions for the actual localized native noise,
not additional regularity assumptions on a weak solution. -/
theorem exists_uniform_path (hc : ∀ ω, Continuous (fun t ↦ U (t, ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ (Y : Parameter → Ω → ℝ) (hYc : ∀ ω, Continuous (fun p ↦ Y p ω)),
      (∀ p, StronglyMeasurable[F (time H p)] (Y p)) ∧
      (∀ n p, ∀ᵐ ω ∂μ, (time H p : WithTop ℝ≥0) <
        ContinuousNormExit.exit (fun t ω ↦ U (t, ω)) n ω →
          Y p ω = observation F U hU hG hβ hβ1 μ H P e n p ω) ∧
      StronglyMeasurable (fun ω ↦ PhysicalHeatParameterSection.path 2 ⟨fun p ↦ Y p ω, hYc ω⟩) ∧
      StronglyMeasurable (fun ω ↦ PhysicalHeatParameterSection.path ∞ ⟨fun p ↦ Y p ω, hYc ω⟩) ∧
      ∀ᵐ ω ∂μ, Tendsto (PhysicalHeatParameterSection.value ∞ ⟨fun p ↦ Y p ω, hYc ω⟩)
        (nhds HeatParameterPullback.initialTime) (nhds 0) := by
  obtain ⟨Y, hYm, hYa, hYc, hYe, hYextra⟩ := exists_version F U hU hG hβ hβ1 μ H P e hc hnull
  refine ⟨Y, hYc, hYa, hYe,
    PhysicalHeatParameterSection.stronglyMeasurable_random_path 2 Y hYm hYc,
    PhysicalHeatParameterSection.stronglyMeasurable_random_path ∞ Y hYm hYc, ?_⟩
  exact hYextra.mono fun ω hω ↦ PhysicalHeatParameterSection.initial_trace ∞
    ⟨fun p ↦ Y p ω, hYc ω⟩ hω.1

end SHEStochastic.UnboundedLocalContinuousVersion
