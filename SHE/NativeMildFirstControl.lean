module

public import SHE.NativeMildFirstResolvent
public import SHE.NativeObservedVolterra
public import SHE.NativeControlMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeMildFirst
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
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : Data 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Exact observed control forcing of the constructed native first
equation. This is the physical deterministic-kernel stochastic Fubini
identity needed to cancel the common additive channel in V-U. -/
theorem control_observation (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) :
    (fun ω => Λ*functional (T-(q:ℝ)) x (NativeClock.volterra Λ (fun s => S.value s ω) q))=ᵐ[μ]
      fun ω => (1-Real.exp (-Λ*(q:ℝ)))*functional T x u₀+
        J.integral (rows 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀ S q hT x) ω-
        J.integral (StoppedInputResolvent.damped 𝓕 μ H
          (rows 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀ S q hT x) hΛ q) ω := by
  filter_upwards [first_resolvent 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ q hq hT x]
    with ω hω
  have hi : Integrable (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*
      functional (T-(s:ℝ)) x (S.value s ω)) (timeMeasure q) := by
    have hc := PositiveGapObservations.coordinate_continuous (T-(q:ℝ)) T x
      (Function.uncurry S.value) (S.continuous ω)
    have hh : Integrable (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*
        PositiveGapObservations.coordinate (T-(q:ℝ)) T x (Function.uncurry S.value) (s,ω))
        (timeMeasure q) := NativeControlMass.continuous_integrable q
      ((show Continuous (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))) by fun_prop).mul hc)
    apply hh.congr
    filter_upwards [timeMeasure_ae_mem q] with s hs
    have hg : T-(q:ℝ)≤T-(s:ℝ) := sub_le_sub_left (by exact_mod_cast hs.2) T
    exact congrArg (fun z : ℝ => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*z)
      (PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr hT)
        (Function.uncurry S.value) x (s,ω) hg)
  have hc := NativeControlMass.centered_integral Λ (functional T x u₀) q hi
  change Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*
    (functional (T-(s:ℝ)) x (S.value s ω)-functional T x u₀) ∂timeMeasure q)=_ at hω
  rw [hc] at hω
  rw [NativeObservedVolterra.observe Λ (S.continuous ω) q hT x]
  change Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*functional (T-(s:ℝ)) x (S.value s ω) ∂timeMeasure q)=_
  linarith

end SHE.NativeMildFirst
