module

public import SHEStochastic.UnboundedNativeHeatEquation
public import SHEStochastic.AEContinuousIntervalClosure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedNativeMildRecognition
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback UnboundedNativeHeatEquation
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

/-- The local native heat equation yields a genuine continuous mild
remainder on the short-time parameter domain. The state equality holds
at every deterministic time strictly inside [0,min(H,1)]; no global
state bound or uniform regularity is supplied as an assumption. Endpoint
and full-horizon extension remain separate steps. -/
theorem fixed_of_local (ξ : Ω → RealL2) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (Y : Parameter → Ω → ℝ) (hYm : ∀ p, Measurable (Y p))
    (hYc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (hYe : ∀ N p, ∀ᵐ ω ∂μ, (time H p : WithTop ℝ≥0) < exit W N ω →
      Y p ω = UnboundedLocalContinuousVersion.observation F (physical W)
        (physical_predictable F W hW) hG hβ hβ1 μ H P e N p ω) :
    ∀ (T : ℝ≥0), T < H → (hT : (T : ℝ) < 1) →
      W T =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ ⟨T, T.property, hT.le⟩ := by
  intro T hTH hT
  have hTnn : T < (1 : ℝ≥0) := by exact_mod_cast hT
  let δ : ℝ≥0 := min (H - T) (1 - T) / 2
  have hδ : 0 < δ := div_pos
    (lt_min (tsub_pos_iff_lt.mpr hTH) (tsub_pos_iff_lt.mpr hTnn)) (by norm_num)
  have hh : δ ≤ min (H - T) (1 - T) := div_le_self zero_le (by norm_num)
  have hTD : T + δ ≤ H := (add_le_add le_rfl (hh.trans (min_le_left _ _))).trans_eq
    (add_tsub_cancel_of_le hTH.le)
  have hTD1nn : T + δ ≤ (1 : ℝ≥0) := (add_le_add le_rfl (hh.trans (min_le_right _ _))).trans_eq
    (add_tsub_cancel_of_le hTnn.le)
  have hTD1 : ((T + δ : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast hTD1nn
  have hn (N : ℕ) : ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0) < exit W N ω → W T ω =
      NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ ⟨T, T.property, hT.le⟩ := by
    apply LocalizedRemainderObservation.state_eq F (UnboundedL2Localization.state (physical W) N)
      (UnboundedL2Localization.predictable F (physical W) (physical_predictable F W hW) N)
      hG hβ hβ1 μ H (UnboundedL2Localization.history_bound (physical W) μ H N) P e
      Y hYm hYc (exit W N) (exit_stopping F W hW hcW N) ?_
      T δ hTH.le hT.le hδ hTD hTD1 ξ (W T) ?_
    · exact hYe N
    · intro x
      exact hEquation N T δ hTH.le hT.le hδ hTD hTD1 x
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  have ht := ContinuousNormExit.tendsto_top (fun t ω ↦ physical W (t, ω)) (physical_continuous W hcW) ω
  rw [WithTop.tendsto_nhds_top_iff] at ht
  obtain ⟨N, hN⟩ := (ht H).exists
  exact hω N ((show (T : WithTop ℝ≥0) ≤ H by exact_mod_cast hTH.le).trans_lt hN)

/-- Construct the local remainder, then reuse the recognition argument. -/
theorem exists_random_version (ξ : Ω → RealL2) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ) :
    ∃ (Y : Parameter → Ω → ℝ) (hc : ∀ ω, Continuous (fun p ↦ Y p ω)),
      (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (time H p)] (Y p)) ∧
      (∀ᵐ ω ∂μ, ∀ p, Y (HeatParameterCoordinates.zeroTime p) ω = 0) ∧
      ∀ (T : ℝ≥0), T < H → (hT : (T : ℝ) < 1) →
        W T =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat T (ξ ω) +
          NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ ⟨T, T.property, hT.le⟩ := by
  obtain ⟨Y, hYm, hYa, hYc, hYe, hExtra⟩ := UnboundedLocalContinuousVersion.exists_version F
    (physical W) (physical_predictable F W hW) hG hβ hβ1 μ H P e
    (physical_continuous W hcW) hnull
  exact ⟨Y, hYc, hYm, hYa, hExtra.mono (fun _ h ↦ h.1),
    fixed_of_local F μ H W hW hG hβ hβ1 P e ξ hcW hEquation Y hYm hYc hYe⟩

/-- The deterministic initial-state interface is retained. -/
theorem exists_version (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀) :
    ∃ (Y : Parameter → Ω → ℝ) (hc : ∀ ω, Continuous (fun p ↦ Y p ω)),
      (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (time H p)] (Y p)) ∧
      (∀ᵐ ω ∂μ, ∀ p, Y (HeatParameterCoordinates.zeroTime p) ω = 0) ∧
      ∀ (T : ℝ≥0), T < H → (hT : (T : ℝ) < 1) →
        (fun ω ↦ W T ω) =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat T u₀ +
          NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ ⟨T, T.property, hT.le⟩ :=
  exists_random_version F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hcW hnull hEquation

/-- The mild representation holds simultaneously on the entire closed
initial interval, including its terminal endpoint. This follows by
continuous-path closure, without an additional moment estimate. -/
theorem close_representation (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (Y : Parameter → Ω → ℝ) (hYc : ∀ ω, Continuous (fun p ↦ Y p ω))
    (hfixed : ∀ (T : ℝ≥0), T < H → (hT : (T : ℝ) < 1) →
      W T =ᵐ[μ] fun ω ↦ NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ ⟨T, T.property, hT.le⟩) :
    ∀ᵐ ω ∂μ, ∀ (T : ℝ≥0), T ≤ H → ∀ hT : (T : ℝ) ≤ 1,
      W T ω = NativeHeatObservation.heat T (ξ ω) +
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hYc ω⟩ ⟨T, T.property, hT⟩ := by
  let Q (ω : Ω) : C(Parameter, ℝ) := ⟨fun p ↦ Y p ω, hYc ω⟩
  let q (r : ℝ) : ShortTime := Set.projIcc (0 : ℝ) 1 zero_le_one r
  let f (r : ℝ) (ω : Ω) := NativePhysicalState.push (W r.toNNReal ω)
  let g (r : ℝ) (ω : Ω) := PhysicalHeatState.state r (NativeHeatObservation.embed (ξ ω)) +
    PhysicalHeatParameterSection.value 2 (Q ω) (q r)
  have hf (ω : Ω) : Continuous (fun r ↦ f r ω) := by
    have hh := NativePhysicalState.push.continuous.comp ((hcW ω).comp continuous_real_toNNReal)
    convert hh using 1 <;> rfl
  have hg (ω : Ω) : Continuous (fun r ↦ g r ω) := by
    have hq : Continuous q := continuous_projIcc
    have hh := (PhysicalHeatState.continuous_state (NativeHeatObservation.embed (ξ ω))).add
      ((PhysicalHeatParameterSection.uniformContinuous_value 2 (Q ω)).continuous.comp hq)
    convert hh using 1 <;> rfl
  have hprefix (r : ℝ) (hr : r ∈ Set.Ico 0 (min (H : ℝ) 1)) : f r =ᵐ[μ] g r := by
    let T : ℝ≥0 := ⟨r, hr.1⟩
    have hTH : T < H := hr.2.trans_le (min_le_left _ _)
    have hT : (T : ℝ) < 1 := hr.2.trans_le (min_le_right _ _)
    have hTeq : r.toNNReal = T := NNReal.eq (Real.coe_toNNReal r hr.1)
    have hproj : q r = (⟨T, T.property, hT.le⟩ : ShortTime) := by
      change Set.projIcc (0 : ℝ) 1 zero_le_one (⟨T, T.property, hT.le⟩ : ShortTime).val = _
      rw [Set.projIcc_val]
    filter_upwards [hfixed T hTH hT] with ω hω
    change NativePhysicalState.push (W r.toNNReal ω) =
      PhysicalHeatState.state r (NativeHeatObservation.embed (ξ ω)) + PhysicalHeatParameterSection.value 2 (Q ω) (q r)
    rw [hTeq, hproj]
    convert (congrArg NativePhysicalState.push hω).trans
      (NativeRemainderObservation.push_mild T.property (ξ ω) (Q ω) ⟨T, T.property, hT.le⟩) using 1 <;> rfl
  have hpos : (0 : ℝ) < min (H : ℝ) 1 := lt_min (by exact_mod_cast hH) (by norm_num)
  have hclosed := AEContinuousIntervalClosure.ae_eq_Icc μ f g hf hg 0 (min (H : ℝ) 1) hpos hprefix
  filter_upwards [hclosed] with ω hω T hTH hT
  apply NativePhysicalState.push.injective
  have hTeq : (T : ℝ).toNNReal = T := NNReal.eq (Real.coe_toNNReal (T : ℝ) T.property)
  have hproj : q (T : ℝ) = (⟨T, T.property, hT⟩ : ShortTime) := by
    change Set.projIcc (0 : ℝ) 1 zero_le_one (⟨T, T.property, hT⟩ : ShortTime).val = _
    rw [Set.projIcc_val]
  have hp := hω (T : ℝ) ⟨T.property, le_min (show (T : ℝ) ≤ H from hTH) hT⟩
  change NativePhysicalState.push (W (T : ℝ).toNNReal ω) =
    PhysicalHeatState.state T (NativeHeatObservation.embed (ξ ω)) + PhysicalHeatParameterSection.value 2 (Q ω) (q T) at hp
  rw [hTeq, hproj] at hp
  exact hp.trans (NativeRemainderObservation.push_mild T.property (ξ ω) (Q ω) ⟨T, T.property, hT⟩).symm

/-- The same closed random-initial representation for the locally
constructed native remainder. -/
theorem exists_closed_random_version (ξ : Ω → RealL2) (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ) :
    ∃ (Y : Parameter → Ω → ℝ) (hc : ∀ ω, Continuous (fun p ↦ Y p ω)),
      (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (time H p)] (Y p)) ∧
      (∀ᵐ ω ∂μ, ∀ p, Y (HeatParameterCoordinates.zeroTime p) ω = 0) ∧
      ∀ᵐ ω ∂μ, ∀ (T : ℝ≥0), T ≤ H → ∀ hT : (T : ℝ) ≤ 1,
        W T ω = NativeHeatObservation.heat T (ξ ω) +
          NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ ⟨T, T.property, hT⟩ := by
  obtain ⟨Y, hYc, hYm, hYa, hzero, hfixed⟩ :=
    exists_random_version F μ H W hW hG hβ hβ1 P e ξ hcW hnull hEquation
  exact ⟨Y, hYc, hYm, hYa, hzero, close_representation μ H W ξ hH hcW Y hYc hfixed⟩

/-- Deterministic initial data specialize the same continuous-path proof. -/
theorem exists_closed_version (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀) :
    ∃ (Y : Parameter → Ω → ℝ) (hc : ∀ ω, Continuous (fun p ↦ Y p ω)),
      (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[F (time H p)] (Y p)) ∧
      (∀ᵐ ω ∂μ, ∀ p, Y (HeatParameterCoordinates.zeroTime p) ω = 0) ∧
      ∀ᵐ ω ∂μ, ∀ (T : ℝ≥0), T ≤ H → ∀ hT : (T : ℝ) ≤ 1,
        W T ω = NativeHeatObservation.heat T u₀ +
          NativeRemainderObservation.remainder ⟨fun p ↦ Y p ω, hc ω⟩ ⟨T, T.property, hT⟩ :=
  exists_closed_random_version F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hH hcW hnull hEquation

theorem initial (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀) : W 0 =ᵐ[μ] fun _ ↦ u₀ := by
  obtain ⟨Y, hYc, _, _, hzero, hrep⟩ :=
    exists_closed_version F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation
  filter_upwards [hzero, hrep] with ω hz hr
  let Q : C(Parameter, ℝ) := ⟨fun p ↦ Y p ω, hYc ω⟩
  have he := hr 0 zero_le (by norm_num)
  change W 0 ω = NativeHeatObservation.heat 0 u₀ + NativeRemainderObservation.remainder Q initialTime at he
  have hrem : NativeRemainderObservation.remainder Q initialTime = 0 := by
    unfold NativeRemainderObservation.remainder
    rw [PhysicalHeatParameterSection.value_initial 2 Q hz, map_zero]
  rw [hrem, add_zero] at he
  simpa only [NativeHeatObservation.heat, zero_div, RealHeat.realHeat_zero, ContinuousLinearMap.id_apply] using he

end SHEStochastic.UnboundedNativeMildRecognition
