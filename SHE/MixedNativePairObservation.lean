module

public import SHE.MixedNativePairConstruction
public import SHE.NativePairObservedFirst
public import SHE.NativePairObservedSecond
public import SHE.NativePairFirstResolvent
public import SHE.NativePairControlObservation
public import SHE.NativePairResolvent

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.MixedNativePairObservedFirst
open MeasureTheory Set Filter PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels StoppedItoInputs DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairObservedFirst_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairObservedFirst_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairObservedFirst_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairObservedFirst_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairObservedFirst_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairObservedFirst_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def rows (t : ℝ≥0) {T : ℝ} (hT : (t:ℝ)<T) (x : HeatCircle) : Process (E := Both RealHaarInput) 𝓕 μ H :=
  TwoChannelItoRows.block 𝓕 μ H
    (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
      (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x)
    (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x)

include hIJ₀ hIJ₁ in
theorem observation (t : ℝ≥0) (ht : t≤H) {T : ℝ} (hT : (t:ℝ)<T) (x : HeatCircle) :
    (fun ω => functional (T-(t:ℝ)) x (S.first t ω))=ᵐ[μ]
      fun ω => functional T x u₀+J.integral (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S t hT x) ω := by
  have h₀ := observe_terminal_integral I₀ (leftIntegral 𝓕 μ H J) hIJ₀ hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x
    (S.additiveInput t) (S.additive_kernel t ht)
  have h₁ := observe_terminal_integral I₁ (rightIntegral 𝓕 μ H J) hIJ₁ hell
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x
    (S.residualInput t) (S.residual_kernel t ht)
  have he := TwoChannelItoRows.integral_block 𝓕 μ H J
    (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
      (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x)
    (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x)
  have heAE := Lp.coeFn_add
    ((leftIntegral 𝓕 μ H J).integral (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
      (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x))
    ((rightIntegral 𝓕 μ H J).integral (NativeObservationProcess.process 𝓕 μ H hell
      (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x))
  filter_upwards [S.first_mild t ht,h₀,h₁,heAE] with ω hU h₀ h₁ heAE
  rw [hU,map_add,map_add,functional_heat (τ := T-(t:ℝ)) (t := (t:ℝ))
    (sub_pos.mpr hT) (show 0≤(t:ℝ) from t.2),
    show T-(t:ℝ)+(t:ℝ)=T by ring,h₀,h₁]
  change _=functional T x u₀+J.integral (TwoChannelItoRows.block 𝓕 μ H _ _) ω
  rw [he,heAE]
  simp only [Pi.add_apply]
  ring

end SHE.MixedNativePairObservedFirst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SHE.MixedNativePairObservedSecond
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairObservedSecond_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairObservedSecond_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairObservedSecond_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairObservedSecond_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairObservedSecond_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairObservedSecond_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
theorem observation (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => functional (T-(q:ℝ)) x (S.second q ω))=ᵐ[μ]
      fun ω => Real.exp (-Λ*(q:ℝ))*functional T x v₀+
        Λ*functional (T-(q:ℝ)) x (NativeClock.volterra Λ (fun s => S.first s ω) q)+
        (leftIntegral 𝓕 μ H J).integral
          (NativeDampedObservation.damped 𝓕 μ H hΛ q
            (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
              (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x)) ω+
        (rightIntegral 𝓕 μ H J).integral
          (NativeDampedObservation.damped 𝓕 μ H hΛ q
            (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
              (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient hT x)) ω := by
  have h₀ := NativeDampedObservation.observe_terminal 𝓕 μ H I₀ (leftIntegral 𝓕 μ H J) hIJ₀
    hΛ hκ hκ.le (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x
    (S.controlledAdditiveInput q) (S.controlled_additive_kernel q hq)
  have h₁ := NativeDampedObservation.observe_terminal 𝓕 μ H I₁ (rightIntegral 𝓕 μ H J) hIJ₁
    hΛ hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient hT x
    (S.controlledResidualInput q) (S.controlled_residual_kernel q hq)
  filter_upwards [S.second_mild q hq,h₀,h₁] with ω hU h₀ h₁
  rw [hU,map_add,map_add,map_add,map_smul,map_smul,
    functional_heat (τ := T-(q:ℝ)) (t := (q:ℝ)) (sub_pos.mpr hT) (show 0≤(q:ℝ) from q.2),
    show T-(q:ℝ)+(q:ℝ)=T by ring,h₀,h₁]
  rfl

end SHE.MixedNativePairObservedSecond

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.MixedNativePairObservedFirst
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
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

theorem stop_rows (q s : ℝ≥0) (hs : s≤q) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    stop 𝓕 μ H (s:ℝ) (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x)=
      rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S s
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
      fun ω => J.integral (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x) ω-
        J.integral (StoppedInputResolvent.damped 𝓕 μ H
          (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x) hΛ q) ω := by
  let δ := T-(q:ℝ)
  have hδ : 0<δ := sub_pos.mpr hT
  let Y : ℝ≥0×Ω→ℝ := fun p =>
    PositiveGapObservations.coordinate δ T x (Function.uncurry S.first) p-functional T x u₀
  have hm : StronglyMeasurable Y :=
    ((PositiveGapObservations.coordinate_predictable 𝓕 δ T x (Function.uncurry S.first)
      S.first_predictable).sub stronglyMeasurable_const).mono (predictable_le_product 𝓕)
  have hRep : ∀ᵐ (s : ℝ≥0) ∂timeMeasure q,
      J.integral (stop 𝓕 μ H (s:ℝ) (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x))=ᵐ[μ]
        fun ω => Y (s,ω) := by
    filter_upwards [timeMeasure_ae_mem q] with s hs
    have hst : (s:ℝ)<T := lt_of_le_of_lt (by exact_mod_cast hs.2) hT
    rw [stop_rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q s hs.2 hT x]
    filter_upwards [observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      s (hs.2.trans hq) hst x] with ω hω
    have hg : δ≤T-(s:ℝ) := sub_le_sub_left (by exact_mod_cast hs.2) T
    change _=PositiveGapObservations.coordinate δ T x (Function.uncurry S.first) (s,ω)-functional T x u₀
    rw [PositiveGapObservations.coordinate_eq_functional hδ _ _ _ hg]
    change _=functional (T-(s:ℝ)) x (S.first s ω)-functional T x u₀
    linarith
  have hr := StoppedStochasticResolvent.resolvent_ae_of_measurable 𝓕 μ H
    (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x) J hΛ q Y hm.aestronglyMeasurable hRep
  rw [stop_rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q q le_rfl hT x] at hr
  filter_upwards [hr] with ω hω
  apply Eq.trans _ hω
  congr 1
  apply integral_congr_ae
  filter_upwards [timeMeasure_ae_mem q] with s hs
  have hg : δ≤T-(s:ℝ) := sub_le_sub_left (by exact_mod_cast hs.2) T
  exact congrArg (fun z : ℝ => Real.exp (-Λ*((q:ℝ)-(s:ℝ))) • z)
    (congrArg (fun z : ℝ => z-functional T x u₀)
      (PositiveGapObservations.coordinate_eq_functional hδ (Function.uncurry S.first) x (s,ω) hg).symm)

end SHE.MixedNativePairObservedFirst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.MixedNativePairObservedFirst
open MeasureTheory Set Filter PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels StoppedItoInputs DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairControlObservation_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairControlObservation_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairControlObservation_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairControlObservation_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairControlObservation_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairControlObservation_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Exact observed control forcing of the constructed native first
equation. This is the physical deterministic-kernel stochastic Fubini
identity needed to cancel the common additive channel in V-U. -/
theorem control_observation (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => Λ*functional (T-(q:ℝ)) x (NativeClock.volterra Λ (fun s => S.first s ω) q))=ᵐ[μ]
      fun ω => (1-Real.exp (-Λ*(q:ℝ)))*functional T x u₀+
        J.integral (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x) ω-
        J.integral (StoppedInputResolvent.damped 𝓕 μ H
          (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x) hΛ q) ω := by
  filter_upwards [first_resolvent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq hT x]
    with ω hω
  have hi : Integrable (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*
      functional (T-(s:ℝ)) x (S.first s ω)) (timeMeasure q) := by
    have hc := PositiveGapObservations.coordinate_continuous (T-(q:ℝ)) T x
      (Function.uncurry S.first) (S.first_continuous ω)
    have hh : Integrable (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*
        PositiveGapObservations.coordinate (T-(q:ℝ)) T x (Function.uncurry S.first) (s,ω))
        (timeMeasure q) := NativeControlMass.continuous_integrable q
      ((show Continuous (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))) by fun_prop).mul hc)
    apply hh.congr
    filter_upwards [timeMeasure_ae_mem q] with s hs
    have hg : T-(q:ℝ)≤T-(s:ℝ) := sub_le_sub_left (by exact_mod_cast hs.2) T
    exact congrArg (fun z : ℝ => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*z)
      (PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr hT)
        (Function.uncurry S.first) x (s,ω) hg)
  have hc := NativeControlMass.centered_integral Λ (functional T x u₀) q hi
  change Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*
    (functional (T-(s:ℝ)) x (S.first s ω)-functional T x u₀) ∂timeMeasure q)=_ at hω
  rw [hc] at hω
  rw [NativeObservedVolterra.observe Λ (S.first_continuous ω) q hT x]
  change Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*functional (T-(s:ℝ)) x (S.first s ω) ∂timeMeasure q)=_
  linarith

end SHE.MixedNativePairObservedFirst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.MixedNativePairResolvent
open MeasureTheory Set Filter PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels StoppedItoInputs DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairResolvent_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairResolvent_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairResolvent_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairResolvent_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairResolvent_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairResolvent_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

theorem damped_rows (hΛ : 0≤Λ) (q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    StoppedInputResolvent.damped 𝓕 μ H
      (MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x) hΛ q=
      TwoChannelItoRows.block 𝓕 μ H
        (NativeDampedObservation.damped 𝓕 μ H hΛ q
          (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
            (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x))
        (NativeDampedObservation.damped 𝓕 μ H hΛ q
          (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
            (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x)) := by
  rw [StoppedInputResolvent.damped,
    MixedNativePairObservedFirst.stop_rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q q le_rfl hT x,
    MixedNativePairObservedFirst.rows,PredictableWeightedAlgebra.weighted_block]
  rfl

include hIJ₀ hIJ₁ in
/-- Literal controlled-difference identity for the constructed native
additive/residual pair. The shared additive channel cancels. The residual
term is the damped difference of the actual common-Haar rows, integrated
by the right restriction of the same full-horizon scalar integral J. -/
theorem difference_observation (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => functional (T-(q:ℝ)) x (S.second q ω-S.first q ω))=ᵐ[μ]
      fun ω => Real.exp (-Λ*(q:ℝ))*functional T x (v₀-u₀)+
        (rightIntegral 𝓕 μ H J).integral
          (NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
            (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
            (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
            S.first_coefficient S.second_coefficient q hT x hΛ) ω := by
  let r₀ := NativeObservationProcess.process 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x
  let rU := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x
  let rV := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient hT x
  let d₀ := NativeDampedObservation.damped 𝓕 μ H hΛ q r₀
  let dU := NativeDampedObservation.damped 𝓕 μ H hΛ q rU
  let dV := NativeDampedObservation.damped 𝓕 μ H hΛ q rV
  let D := NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ
  have hD : D=dV-dU := by
    exact PredictableWeightedAlgebra.weighted_sub 𝓕 μ H (PredictableDamping.weight Λ q)
      (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q) rV rU
  have he := congrArg J.integral (damped_rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ q hT x)
  rw [TwoChannelItoRows.integral_block] at he
  have hsum := Lp.coeFn_add ((leftIntegral 𝓕 μ H J).integral d₀) ((rightIntegral 𝓕 μ H J).integral dU)
  rw [← he] at hsum
  have heD := congrArg (rightIntegral 𝓕 μ H J).integral hD
  rw [map_sub] at heD
  have hdiff := Lp.coeFn_sub ((rightIntegral 𝓕 μ H J).integral dV) ((rightIntegral 𝓕 μ H J).integral dU)
  rw [← heD] at hdiff
  filter_upwards [MixedNativePairObservedFirst.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ q hq hT x,
    MixedNativePairObservedSecond.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq hT x,
    MixedNativePairObservedFirst.control_observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq hT x,
    hsum,hdiff] with ω hfirst hsecond hcontrol hsum hdiff
  rw [map_sub,map_sub,hfirst,hsecond,hcontrol,hsum]
  change _=Real.exp (-Λ*(q:ℝ))*(functional T x v₀-functional T x u₀)+
    (rightIntegral 𝓕 μ H J).integral D ω
  rw [hdiff]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

end SHE.MixedNativePairResolvent
