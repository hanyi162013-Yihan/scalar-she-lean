module

public import SHE.NativePairControlObservation
public import SHE.NativePairObservedSecond
public import SHE.PredictableWeightedAlgebra
public import SHE.NativeHybridInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativePairResolvent
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
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

theorem damped_rows (hΛ : 0≤Λ) (q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    StoppedInputResolvent.damped 𝓕 μ H
      (NativePairObservedFirst.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x) hΛ q=
      TwoChannelItoRows.block 𝓕 μ H
        (NativeDampedObservation.damped 𝓕 μ H hΛ q
          (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
            (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x))
        (NativeDampedObservation.damped 𝓕 μ H hΛ q
          (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
            (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient hT x)) := by
  rw [StoppedInputResolvent.damped,
    NativePairObservedFirst.stop_rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q q le_rfl hT x,
    NativePairObservedFirst.rows,PredictableWeightedAlgebra.weighted_block]
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
          (NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
            (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
            (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
            S.first_coefficient S.second_coefficient q hT x hΛ) ω := by
  let r₀ := NativeObservationProcess.process 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x
  let rU := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient hT x
  let rV := NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second) S.second_coefficient hT x
  let d₀ := NativeDampedObservation.damped 𝓕 μ H hΛ q r₀
  let dU := NativeDampedObservation.damped 𝓕 μ H hΛ q rU
  let dV := NativeDampedObservation.damped 𝓕 μ H hΛ q rV
  let D := NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ
  have hD : D=dV-dU := by
    exact PredictableWeightedAlgebra.weighted_sub 𝓕 μ H (PredictableDamping.weight Λ q)
      (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q) rV rU
  have he := congrArg J.integral (damped_rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S hΛ q hT x)
  rw [TwoChannelItoRows.integral_block] at he
  have hsum := Lp.coeFn_add ((leftIntegral 𝓕 μ H J).integral d₀) ((rightIntegral 𝓕 μ H J).integral dU)
  rw [← he] at hsum
  have heD := congrArg (rightIntegral 𝓕 μ H J).integral hD
  rw [map_sub] at heD
  have hdiff := Lp.coeFn_sub ((rightIntegral 𝓕 μ H J).integral dV) ((rightIntegral 𝓕 μ H J).integral dU)
  rw [← heD] at hdiff
  filter_upwards [NativePairObservedFirst.observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ q hq hT x,
    NativePairObservedSecond.observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq hT x,
    NativePairObservedFirst.control_observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq hT x,
    hsum,hdiff] with ω hfirst hsecond hcontrol hsum hdiff
  rw [map_sub,map_sub,hfirst,hsecond,hcontrol,hsum]
  change _=Real.exp (-Λ*(q:ℝ))*(functional T x v₀-functional T x u₀)+
    (rightIntegral 𝓕 μ H J).integral D ω
  rw [hdiff]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

end SHE.NativePairResolvent
