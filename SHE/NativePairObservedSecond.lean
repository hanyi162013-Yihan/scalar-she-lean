module

public import SHE.NativePairObservedFirst
public import SHE.NativeDampedObservation
public import SHE.NativeObservedVolterra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativePairObservedSecond
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
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
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
            (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
              (ContinuousHeatMild.coefficientFunction ha hell hb S.second) S.second_coefficient hT x)) ω := by
  have h₀ := NativeDampedObservation.observe_terminal 𝓕 μ H I₀ (leftIntegral 𝓕 μ H J) hIJ₀
    hΛ hκ hκ.le (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x
    (S.controlledAdditiveInput q) (S.controlled_additive_kernel q hq)
  have h₁ := NativeDampedObservation.observe_terminal 𝓕 μ H I₁ (rightIntegral 𝓕 μ H J) hIJ₁
    hΛ hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second) S.second_coefficient hT x
    (S.controlledResidualInput q) (S.controlled_residual_kernel q hq)
  filter_upwards [S.second_mild q hq,h₀,h₁] with ω hU h₀ h₁
  rw [hU,map_add,map_add,map_add,map_smul,map_smul,
    functional_heat (τ := T-(q:ℝ)) (t := (q:ℝ)) (sub_pos.mpr hT) (show 0≤(q:ℝ) from q.2),
    show T-(q:ℝ)+(q:ℝ)=T by ring,h₀,h₁]
  rfl

end SHE.NativePairObservedSecond
