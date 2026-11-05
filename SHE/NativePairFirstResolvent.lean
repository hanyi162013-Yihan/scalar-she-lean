module

public import SHE.NativePairObservedFirst

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.NativePairObservedFirst
open MeasureTheory Set Filter PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels StoppedItoInputs DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairFirstResolvent_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairFirstResolvent_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairFirstResolvent_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairFirstResolvent_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairFirstResolvent_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairFirstResolvent_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

theorem stop_rows (q s : ℝ≥0) (hs : s≤q) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    stop 𝓕 μ H (s:ℝ) (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x)=
      rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S s
        (lt_of_le_of_lt (by exact_mod_cast hs) hT) x := by
  unfold rows
  rw [TwoChannelItoRows.stop_block,LocalNativeObservations.stop_observation_process,
    LocalNativeObservations.stop_observation_process]
  simp only [min_eq_left hs]

include hIJ₀ hIJ₁ in
/-- Actual stochastic resolvent for the constructed first equation,
observed at any later original target T. The noise horizon remains H,
even if T lies below H. Joint integrability is derived from the same
stopped-row Itô isometry and actual predictable state. -/
theorem first_resolvent (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => Λ • (∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ))) •
      (functional (T-(s:ℝ)) x (S.first s ω)-functional T x u₀) ∂timeMeasure q))=ᵐ[μ]
      fun ω => J.integral (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x) ω-
        J.integral (StoppedInputResolvent.damped 𝓕 μ H
          (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x) hΛ q) ω := by
  let δ := T-(q:ℝ)
  have hδ : 0<δ := sub_pos.mpr hT
  let Y : ℝ≥0×Ω→ℝ := fun p =>
    PositiveGapObservations.coordinate δ T x (Function.uncurry S.first) p-functional T x u₀
  have hm : StronglyMeasurable Y :=
    ((PositiveGapObservations.coordinate_predictable 𝓕 δ T x (Function.uncurry S.first)
      S.first_predictable).sub stronglyMeasurable_const).mono (predictable_le_product 𝓕)
  have hRep : ∀ᵐ (s : ℝ≥0) ∂timeMeasure q,
      J.integral (stop 𝓕 μ H (s:ℝ) (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x))=ᵐ[μ]
        fun ω => Y (s,ω) := by
    filter_upwards [timeMeasure_ae_mem q] with s hs
    have hst : (s:ℝ)<T := lt_of_le_of_lt (by exact_mod_cast hs.2) hT
    rw [stop_rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q s hs.2 hT x]
    filter_upwards [observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      s (hs.2.trans hq) hst x] with ω hω
    have hg : δ≤T-(s:ℝ) := sub_le_sub_left (by exact_mod_cast hs.2) T
    change _=PositiveGapObservations.coordinate δ T x (Function.uncurry S.first) (s,ω)-functional T x u₀
    rw [PositiveGapObservations.coordinate_eq_functional hδ _ _ _ hg]
    change _=functional (T-(s:ℝ)) x (S.first s ω)-functional T x u₀
    linarith
  have hr := StoppedStochasticResolvent.resolvent_ae_of_measurable 𝓕 μ H
    (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x) J hΛ q Y hm.aestronglyMeasurable hRep
  rw [stop_rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q q le_rfl hT x] at hr
  filter_upwards [hr] with ω hω
  apply Eq.trans _ hω
  congr 1
  apply integral_congr_ae
  filter_upwards [timeMeasure_ae_mem q] with s hs
  have hg : δ≤T-(s:ℝ) := sub_le_sub_left (by exact_mod_cast hs.2) T
  exact congrArg (fun z : ℝ => Real.exp (-Λ*((q:ℝ)-(s:ℝ))) • z)
    (congrArg (fun z : ℝ => z-functional T x u₀)
      (PositiveGapObservations.coordinate_eq_functional hδ (Function.uncurry S.first) x (s,ω) hg).symm)

end SHE.NativePairObservedFirst
