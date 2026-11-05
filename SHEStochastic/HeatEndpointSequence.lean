module

public import SHE.HeatObservationEndpointLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.HeatEndpointSequence
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- A prescribed sequence of positive-age observations suffices for
the original scalar endpoint argument. This permits vector components
to reuse it with targets confined to the original finite horizon. -/
theorem identify_random (J : StandardTerminalIto (C := C) F μ H) (U : Ω → RealL2) (hU : Measurable U)
    (ε : ℕ → ℝ) (hε : ∀ j, 0<ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℕ → HeatCircle → Process (E := C) F μ H) (R0 : HeatCircle → Process (E := C) F μ H)
    (hR : ∀ x, Tendsto (fun j => R j x) atTop (𝓝 (R0 x)))
    (a : ℕ → HeatCircle → Ω → ℝ) (a0 : HeatCircle → Ω → ℝ)
    (ha : ∀ x ω, Tendsto (fun j => a j x ω) atTop (𝓝 (a0 x ω)))
    (hobs : ∀ j x, (fun ω => NativeHeatObservation.functional (ε j) x (U ω)) =ᵐ[μ]
      fun ω => a j x ω+J.integral (R j x) ω) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      PredictableScalarField.nativeField U (ω,x)=a0 x ω+J.integral (R0 x) ω := by
  obtain ⟨ns,hns,hphys⟩ := HeatPhysicalSubsequence.exists_subsequence U hU μ ε
    (tendsto_nhdsWithin_iff.mpr ⟨hε0,Filter.Eventually.of_forall hε⟩)
  have hp := (Measure.measurePreserving_swap (μ := AddCircle.haarAddCircle (T := 2*Real.pi)) (ν := μ)).quasiMeasurePreserving.ae hphys
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with x hx
  have hi := J.integral.continuous.continuousAt.tendsto.comp ((hR x).comp hns.tendsto_atTop)
  obtain ⟨ms,hms,hnoise⟩ := (tendstoInMeasure_of_tendsto_Lp hi).exists_seq_tendsto_ae
  filter_upwards [hx,hnoise,ae_all_iff.mpr (fun j => hobs j x)] with ω hω hn ho
  have hl : Tendsto (fun j => NativeHeatObservation.functional (ε (ns j)) x (U ω)) atTop
      (𝓝 (PredictableScalarField.nativeField U (ω,x))) := by
    simpa only [NativeHeatObservation.functional_physical (hε _),Prod.swap,Prod.fst,Prod.snd] using hω
  have hr := ((ha x ω).comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).add hn
  have hr' : Tendsto (fun j => NativeHeatObservation.functional (ε (ns (ms j))) x (U ω)) atTop
      (𝓝 (a0 x ω+J.integral (R0 x) ω)) := by
    apply hr.congr'
    filter_upwards with j
    exact (ho (ns (ms j))).symm
  exact tendsto_nhds_unique (hl.comp hms.tendsto_atTop) hr'


theorem identify (J : StandardTerminalIto (C := C) F μ H) (U : Ω → RealL2) (hU : Measurable U)
    (ε : ℕ → ℝ) (hε : ∀ j, 0<ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℕ → HeatCircle → Process (E := C) F μ H) (R0 : HeatCircle → Process (E := C) F μ H)
    (hR : ∀ x, Tendsto (fun j => R j x) atTop (𝓝 (R0 x)))
    (a : ℕ → HeatCircle → ℝ) (a0 : HeatCircle → ℝ)
    (ha : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (a0 x)))
    (hobs : ∀ j x, (fun ω => NativeHeatObservation.functional (ε j) x (U ω)) =ᵐ[μ]
      fun ω => a j x+J.integral (R j x) ω) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      PredictableScalarField.nativeField U (ω,x)=a0 x+J.integral (R0 x) ω := by
  exact identify_random J U hU ε hε hε0 R R0 hR (fun j x _ => a j x) (fun x _ => a0 x)
    (fun x _ => ha x) hobs

end SHEStochastic.HeatEndpointSequence
