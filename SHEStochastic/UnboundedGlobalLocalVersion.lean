module

public import SHEStochastic.UnboundedGlobalHeatContinuity
public import SHEStochastic.UnboundedLocalizedHeatRows
public import SHEStochastic.NativeFieldLocalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalLocalVersion
open MeasureTheory SHE SHE.PredictableL2 AddCircle Filter
open HeatParameterCover HeatParameterCoordinates
open scoped NNReal ENNReal Topology

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi))))

def observation (n : ℕ) : Parameter → Ω → ℝ :=
  UnboundedGlobalHeatContinuity.observation F (UnboundedL2Localization.state U n)
    (UnboundedL2Localization.predictable F U hU n) hG hβ hβ1 μ H
    (UnboundedL2Localization.history_bound U μ H n) P e

theorem observation_adapted (hnull : NullCompleteFiltration.ContainsNullSets F μ) (n : ℕ) (p : Parameter) :
    StronglyMeasurable[F (GlobalHeatParameter.time H p)] (observation F U hU hG hβ hβ1 μ H P e n p) := by
  let u := UnboundedLocalizedHeatRows.globalRow F U hU hG hβ hβ1 μ H n (GlobalHeatParameter.time H p)
    (GlobalHeatParameter.time_le_horizon H p) (center p)
  have hu : StoppedItoInputs.stop F μ H (GlobalHeatParameter.time H p) u=u :=
    UnboundedFiniteHorizonInput.input_stop F _ _ hG hβ hβ1 μ H (GlobalHeatParameter.time H p)
      (GlobalHeatParameter.time_le_horizon H p) (center p) _
  obtain ⟨Z,hZ,he⟩ := StoppedItoInputs.stopped_integral_adapted F μ H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (GlobalHeatParameter.time H p) u
  rw [hu] at he
  exact NullCompleteFiltration.stronglyMeasurable_congr F μ hnull (GlobalHeatParameter.time H p) hZ he

/-- An adapted continuous local native convolution on the full finite
horizon. Its compact bound and zero initial trace are conclusions;
there is no deterministic bound on the original L2 state. -/
theorem exists_version (hc : ∀ ω, Continuous (fun t ↦ U (t,ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Y : Parameter → Ω → ℝ, (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (GlobalHeatParameter.time H p)] (Y p)) ∧
      (∀ ω, Continuous (fun p ↦ Y p ω)) ∧
      (∀ n p, ∀ᵐ ω ∂μ, (GlobalHeatParameter.time H p:WithTop ℝ≥0)<
        ContinuousNormExit.exit (fun t ω ↦ U (t,ω)) n ω → Y p ω=observation F U hU hG hβ hβ1 μ H P e n p ω) ∧
      ∀ᵐ ω ∂μ, (∀ p, Y (zeroTime p) ω=0) ∧
        (∃ M : ℝ, 0≤M ∧ ∀ p, |Y p ω|≤M) ∧
        ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ p : Parameter, |p.val 0|<δ → |Y p ω|<ε := by
  let τ := ContinuousNormExit.exit (fun t ω ↦ U (t,ω))
  have hτ (ω : Ω) : Tendsto (fun n ↦ τ n ω) atTop (nhds ⊤) :=
    ContinuousNormExit.tendsto_top (fun t ω ↦ U (t,ω)) hc ω
  have hescape : ∀ ω, ∃ n, (H:WithTop ℝ≥0)<τ n ω := by
    intro ω
    have ht := hτ ω
    rw [WithTop.tendsto_nhds_top_iff] at ht
    exact (ht H).exists
  have hv (n : ℕ) : ∃ Z : Parameter → Ω → ℝ, (∀ p, Measurable (Z p)) ∧
      (∀ p, Z p=ᵐ[μ] observation F U hU hG hβ hβ1 μ H P e n p) ∧
      (∀ ω, Continuous (fun p ↦ Z p ω)) ∧ ∀ᵐ ω ∂μ, ∀ p, Z (zeroTime p) ω=0 := by
    obtain ⟨Z,hm,he,hc,hz⟩ := UnboundedGlobalHeatContinuity.exists_closed_version F
      (UnboundedL2Localization.state U n) (UnboundedL2Localization.predictable F U hU n)
      hG hβ hβ1 μ H (UnboundedL2Localization.history_bound U μ H n) P e
    exact ⟨Z,hm,he,hc,hz.mono fun ω hω ↦ hω.1⟩
  have hcompat (n m : ℕ) (p : Parameter) : ∀ᵐ ω ∂μ,
      (GlobalHeatParameter.time H p:WithTop ℝ≥0)<τ n ω →
      (GlobalHeatParameter.time H p:WithTop ℝ≥0)<τ m ω →
        observation F U hU hG hβ hβ1 μ H P e n p ω=observation F U hU hG hβ hβ1 μ H P e m p ω := by
    have hh := UnboundedLocalizedHeatRows.global_native_eq_before F U hU hG hβ hβ1 μ H hc
      (min n m) n m (GlobalHeatParameter.time H p) (by exact_mod_cast Nat.min_le_left n m)
      (by exact_mod_cast Nat.min_le_right n m) (GlobalHeatParameter.time_le_horizon H p) (center p) P e hnull
    filter_upwards [hh] with ω he hpn hpm
    apply he
    rcases le_total n m with h | h
    · simpa only [min_eq_left h] using hpn.le
    · simpa only [min_eq_right h] using hpm.le
  obtain ⟨Y,hYm,hYc,hYe,hZero⟩ := LocalizedFieldAssembly.exists_of_modifications H τ hescape μ
    (GlobalHeatParameter.time H) (GlobalHeatParameter.time_le_horizon H)
    (observation F U hU hG hβ hβ1 μ H P e) zeroTime hv hcompat (fun n ↦ by
      simpa only [Set.compl_setOf, not_le] using
        ((F.le H) _ (UnboundedL2Localization.exit_stopping F U hU hc n H)).compl)
  have hYa (p : Parameter) : StronglyMeasurable[F (GlobalHeatParameter.time H p)] (Y p) :=
    NativeFieldLocalization.adapted F μ hnull (GlobalHeatParameter.time H p) τ hτ
      (fun n ↦ observation F U hU hG hβ hβ1 μ H P e n p)
      (fun n ↦ observation_adapted F U hU hG hβ hβ1 μ H P e hnull n p) (Y p) (fun n ↦ hYe n p)
  refine ⟨Y,hYm,hYa,hYc,hYe,?_⟩
  filter_upwards [hZero] with ω hω
  exact ⟨hω,HeatParameterInitialBound.bounded (fun p ↦ Y p ω) (hYc ω),
    fun _ hε ↦ HeatParameterInitialBound.uniformly_small (fun p ↦ Y p ω) (hYc ω) hω hε⟩

end SHEStochastic.UnboundedGlobalLocalVersion
