module

public import SHE.NativeMildFirstControl
public import SHE.NativeDampedHaarInput
public import SHE.NativeDampedObservation
public import SHE.PredictableWeightedAlgebra
public import SHE.HeatObservationUniqueness
public import SHE.NativeObservedVolterra
public import SHE.NativeControlMass

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeFirstDampedMild
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
variable (S : NativeMildFirst.Data 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))


variable(hΛ:0≤Λ)(hH:(H:ℝ)≤1)
local notation "f0"=>fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ
local notation "f1"=>ContinuousHeatMild.coefficientFunction ha hell hb S.value
local notation "hM"=>hell.le.trans ((hb 0).1.trans (hb 0).2)

def additive(q:ℝ≥0)(hq:q≤H):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  NativeDampedHaarInput.input 𝓕 μ H hΛ hκ hκ.le f0 stronglyMeasurable_const q hq
    ((show (q:ℝ)≤H by exact_mod_cast hq).trans hH)

def residual(q:ℝ≥0)(hq:q≤H):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM f1 S.coefficient q hq
    ((show (q:ℝ)≤H by exact_mod_cast hq).trans hH)
local notation "a0"=>additive 𝓕 μ H Λ κ hκ hΛ hH
local notation "a1"=>residual (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (ha:=ha) (hell:=hell) (hb:=hb) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (hΛ:=hΛ) (hH:=hH)

theorem damped_rows(q:ℝ≥0){T:ℝ}(hT:(q:ℝ)<T)(x:HeatCircle):
    StoppedInputResolvent.damped 𝓕 μ H
      (NativeMildFirst.rows 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀ S q hT x) hΛ q=
      TwoChannelItoRows.block 𝓕 μ H
        (NativeDampedObservation.damped 𝓕 μ H hΛ q
          (NativeObservationProcess.process 𝓕 μ H hκ hκ.le f0 stronglyMeasurable_const hT x))
        (NativeDampedObservation.damped 𝓕 μ H hΛ q
          (NativeObservationProcess.process 𝓕 μ H hell hM f1 S.coefficient hT x)):=by
  rw [StoppedInputResolvent.damped,
    NativeMildFirst.stop_rows 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀ S q q le_rfl hT x,
    NativeMildFirst.rows,PredictableWeightedAlgebra.weighted_block]
  rfl

include hIJ₀ hIJ₁ in
theorem observed(q:ℝ≥0)(hq:q≤H){T:ℝ}(hT:(q:ℝ)<T)(x:HeatCircle):
    (fun ω=>functional (T-(q:ℝ)) x (S.value q ω))=ᵐ[μ]
      (fun ω=>functional (T-(q:ℝ)) x
        (Real.exp (-Λ*(q:ℝ)) • NativeHeatObservation.heat (q:ℝ) u₀+
          Λ • NativeClock.volterra Λ (fun s=>S.value s ω) q+
          I₀.integral (a0 q hq) ω+I₁.integral (a1 q hq) ω)):=by
  let r0:=NativeObservationProcess.process 𝓕 μ H hκ hκ.le f0 stronglyMeasurable_const hT x
  let r1:=NativeObservationProcess.process 𝓕 μ H hell hM f1 S.coefficient hT x
  let d0:=NativeDampedObservation.damped 𝓕 μ H hΛ q r0
  let d1:=NativeDampedObservation.damped 𝓕 μ H hΛ q r1
  have ha0:a0 q hq=ᵐ[energyMeasure μ H] fun p=>Real.exp (-Λ*((q:ℝ)-(p.1:ℝ))) •
      NativeHeatObservation.kernel κ κ hκ ((q:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ):=
    NativeDampedHaarInput.input_ae 𝓕 μ H hΛ hκ hκ.le f0 stronglyMeasurable_const q hq
      ((show (q:ℝ)≤H by exact_mod_cast hq).trans hH)
  have ha1:a1 q hq=ᵐ[energyMeasure μ H] fun p=>Real.exp (-Λ*((q:ℝ)-(p.1:ℝ))) •
      NativeHeatObservation.kernel ell M hell ((q:ℝ)-(p.1:ℝ),f1 p):=
    NativeDampedHaarInput.input_ae 𝓕 μ H hΛ hell hM f1 S.coefficient q hq
      ((show (q:ℝ)≤H by exact_mod_cast hq).trans hH)
  have h0:=NativeDampedObservation.observe_terminal 𝓕 μ H I₀ (leftIntegral 𝓕 μ H J) hIJ₀
    hΛ hκ hκ.le f0 stronglyMeasurable_const hT x (a0 q hq) ha0
  have h1:=NativeDampedObservation.observe_terminal 𝓕 μ H I₁ (rightIntegral 𝓕 μ H J) hIJ₁
    hΛ hell hM f1 S.coefficient hT x (a1 q hq) ha1
  have hadd:=Lp.coeFn_add ((leftIntegral 𝓕 μ H J).integral d0) ((rightIntegral 𝓕 μ H J).integral d1)
  have he:=NativeMildFirst.control_observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ q hq hT x
  rw [damped_rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ S hΛ q hT x,
    TwoChannelItoRows.integral_block] at he
  filter_upwards [NativeMildFirst.observation 𝓕 μ H κ hκ ha hell hb I₀ I₁ u₀ S J hIJ₀ hIJ₁ q hq hT x,
    he,h0,h1,hadd] with ω ho hc h0 h1 hadd
  have hh : functional (T-(q:ℝ)) x (NativeHeatObservation.heat (q:ℝ) u₀)=functional T x u₀ := by
    have ht := NativeHeatObservation.functional_heat (τ:=T-(q:ℝ)) (t:=(q:ℝ))
      (sub_pos.mpr hT) q.2 x u₀
    simpa only [show T-(q:ℝ)+(q:ℝ)=T by ring] using ht
  simp only [map_add,map_smul] 
  simp only [hh]
  change _=Real.exp (-Λ*(q:ℝ))*functional T x u₀+
    Λ*functional (T-(q:ℝ)) x (NativeClock.volterra Λ (fun s=>S.value s ω) q)+
    functional (T-(q:ℝ)) x (I₀.integral (a0 q hq) ω)+
    functional (T-(q:ℝ)) x (I₁.integral (a1 q hq) ω)
  rw [hadd] at hc
  change _=_-((leftIntegral 𝓕 μ H J).integral d0 ω+(rightIntegral 𝓕 μ H J).integral d1 ω) at hc
  change _=(leftIntegral 𝓕 μ H J).integral d0 ω at h0
  change _=(rightIntegral 𝓕 μ H J).integral d1 ω at h1
  linarith
end SHE.NativeFirstDampedMild
