module

public import SHEStochastic.UnboundedGlobalNativeEquation
public import SHEStochastic.UnboundedGlobalLocalVersion
public import SHEStochastic.GlobalLocalizedRemainderObservation
public import SHEStochastic.AEContinuousIntervalClosure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalMildRecognition
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedNativeHeatEquation
open GlobalHeatRowPhysicalIntegration
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)

/-- The original global localized equation identifies the actual L2 state
with its heat orbit and the constructed convolution at every interior time. -/
theorem fixed_of_local (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (Y : Parameter → Ω → ℝ) (hYm : ∀ p, Measurable (Y p))
    (hYc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (hYe : ∀ N p, ∀ᵐ ω ∂μ, (GlobalHeatParameter.time H p : WithTop ℝ≥0) < exit W N ω →
      Y p ω = UnboundedGlobalLocalVersion.observation F (physical W)
        (physical_predictable F W hW) hG hβ hβ1 μ H P e N p ω) :
    ∀ (T : ℝ≥0) (hTH : T < H),
      W T =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ (unitTime H hH T hTH.le) := by
  intro T hTH
  let δ : ℝ≥0 := (H - T) / 2
  have hδ : 0 < δ := div_pos (tsub_pos_iff_lt.mpr hTH) (by norm_num)
  have hh : δ ≤ H - T := div_le_self zero_le (by norm_num)
  have hTD : T + δ ≤ H := (add_le_add le_rfl hh).trans_eq (add_tsub_cancel_of_le hTH.le)
  have hn (N : ℕ) : ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω → W T ω =
      NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ (unitTime H hH T hTH.le) := by
    apply GlobalLocalizedRemainderObservation.state_eq F (UnboundedL2Localization.state (physical W) N)
      (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N)
      hG hβ hβ1 μ H hH (UnboundedL2Localization.history_bound (physical W) μ H N) P e
      Y hYm hYc (exit W N) (exit_stopping F W hW hcW N) (hYe N)
      T δ hTH.le hδ hTD ξ (W T)
    intro x
    exact hEquation N T δ hTH.le hδ hTD x
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  have ht := ContinuousNormExit.tendsto_top (fun t ω ↦ physical W (t, ω)) (physical_continuous W hcW) ω
  rw [WithTop.tendsto_nhds_top_iff] at ht
  obtain ⟨N, hN⟩ := (ht H).exists
  exact hω N ((show (T : WithTop ℝ≥0) ≤ H by exact_mod_cast hTH.le).trans_lt hN)

/-- A global remainder is constructed internally from the native noise,
without a uniform state bound or an assumed continuous modification. -/
theorem exists_random_version (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ) :
    ∃ (Y : Parameter → Ω → ℝ) (hc : ∀ ω, Continuous (fun p ↦ Y p ω)),
      (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (GlobalHeatParameter.time H p)] (Y p)) ∧
      (∀ᵐ ω ∂μ, ∀ p, Y (HeatParameterCoordinates.zeroTime p) ω = 0) ∧
      ∀ (T : ℝ≥0) (hTH : T < H),
        W T =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat T (ξ ω) +
          NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ (unitTime H hH T hTH.le) := by
  obtain ⟨Y, hYm, hYa, hYc, hYe, hExtra⟩ := UnboundedGlobalLocalVersion.exists_version F
    (physical W) (physical_predictable F W hW) hG hβ hβ1 μ H P e
    (physical_continuous W hcW) hnull
  exact ⟨Y, hYc, hYm, hYa, hExtra.mono (fun _ h ↦ h.1),
    fixed_of_local F μ H W hW hG hβ hβ1 P e ξ hH hcW hEquation Y hYm hYc hYe⟩

/-- Close the native mild identity simultaneously on the entire finite
horizon. The physical heat age is T while the compact time parameter is T/H. -/
theorem close_representation (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (Y : Parameter → Ω → ℝ) (hYc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (hfixed : ∀ (T : ℝ≥0) (hTH : T < H),
      W T =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ (unitTime H hH T hTH.le)) :
    ∀ᵐ ω ∂μ, ∀ (T : ℝ≥0) (hTH : T ≤ H),
      W T ω = NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ (unitTime H hH T hTH) := by
  let Q (ω : Ω) : C(Parameter, ℝ) := ⟨fun p ↦ Y p ω, hYc ω⟩
  let q (r : ℝ) : ShortTime := Set.projIcc (0 : ℝ) 1 zero_le_one (r/(H:ℝ))
  let f (r : ℝ) (ω : Ω) := NativePhysicalState.push (W r.toNNReal ω)
  let g (r : ℝ) (ω : Ω) := PhysicalHeatState.state r (NativeHeatObservation.embed (ξ ω)) +
    PhysicalHeatParameterSection.value 2 (Q ω) (q r)
  have hf (ω : Ω) : Continuous (fun r ↦ f r ω) := by
    exact NativePhysicalState.push.continuous.comp ((hcW ω).comp continuous_real_toNNReal)
  have hg (ω : Ω) : Continuous (fun r ↦ g r ω) := by
    have hq : Continuous q := continuous_projIcc.comp (continuous_id.div_const _)
    exact (PhysicalHeatState.continuous_state (NativeHeatObservation.embed (ξ ω))).add
      ((PhysicalHeatParameterSection.uniformContinuous_value 2 (Q ω)).continuous.comp hq)
  have hproj (T : ℝ≥0) (hTH : T ≤ H) : q (T:ℝ) = unitTime H hH T hTH := by
    change Set.projIcc (0:ℝ) 1 zero_le_one (unitTime H hH T hTH).val = _
    rw [Set.projIcc_val]
  have hprefix (r : ℝ) (hr : r ∈ Set.Ico 0 (H:ℝ)) : f r =ᵐ[μ] g r := by
    let T : ℝ≥0 := ⟨r, hr.1⟩
    have hTH : T < H := hr.2
    have hTeq : r.toNNReal = T := NNReal.eq (Real.coe_toNNReal r hr.1)
    filter_upwards [hfixed T hTH] with ω hω
    change NativePhysicalState.push (W r.toNNReal ω) =
      PhysicalHeatState.state r (NativeHeatObservation.embed (ξ ω)) + PhysicalHeatParameterSection.value 2 (Q ω) (q r)
    rw [hTeq]
    change NativePhysicalState.push (W T ω) =
      PhysicalHeatState.state T (NativeHeatObservation.embed (ξ ω)) + PhysicalHeatParameterSection.value 2 (Q ω) (q (T:ℝ))
    rw [hproj T hTH.le]
    convert (congrArg NativePhysicalState.push hω).trans
      (NativeRemainderObservation.push_mild T.property (ξ ω) (Q ω) (unitTime H hH T hTH.le)) using 1 <;> rfl
  have hclosed := AEContinuousIntervalClosure.ae_eq_Icc μ f g hf hg 0 (H:ℝ) hH hprefix
  filter_upwards [hclosed] with ω hω T hTH
  apply NativePhysicalState.push.injective
  have hTeq : (T : ℝ).toNNReal = T := NNReal.eq (Real.coe_toNNReal (T : ℝ) T.property)
  have hp := hω (T : ℝ) ⟨T.property, hTH⟩
  change NativePhysicalState.push (W (T : ℝ).toNNReal ω) =
    PhysicalHeatState.state T (NativeHeatObservation.embed (ξ ω)) + PhysicalHeatParameterSection.value 2 (Q ω) (q T) at hp
  rw [hTeq, hproj T hTH] at hp
  exact hp.trans (NativeRemainderObservation.push_mild T.property (ξ ω) (Q ω) (unitTime H hH T hTH)).symm

/-- Full closed-horizon random-initial native mild recognition. -/
theorem exists_closed_random_version (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ) :
    ∃ (Y : Parameter → Ω → ℝ) (hc : ∀ ω, Continuous (fun p ↦ Y p ω)),
      (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (GlobalHeatParameter.time H p)] (Y p)) ∧
      (∀ᵐ ω ∂μ, ∀ p, Y (HeatParameterCoordinates.zeroTime p) ω = 0) ∧
      ∀ᵐ ω ∂μ, ∀ (T : ℝ≥0) (hTH : T ≤ H),
        W T ω = NativeHeatObservation.heat T (ξ ω) +
          NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ (unitTime H hH T hTH) := by
  obtain ⟨Y,hYc,hYm,hYa,hzero,hfixed⟩ :=
    exists_random_version F μ H W hW hG hβ hβ1 P e ξ hH hcW hnull hEquation
  exact ⟨Y,hYc,hYm,hYa,hzero,close_representation μ H W ξ hH hcW Y hYc hfixed⟩

end SHEStochastic.UnboundedGlobalMildRecognition
