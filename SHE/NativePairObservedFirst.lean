module

public import SHE.NativePairConstruction
public import SHE.LocalTwoChannelObservations
public import SHE.StoppedVersionIntegrability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.NativePairObservedFirst
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
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def rows (t : ℝ≥0) {T : ℝ} (hT : (t:ℝ)<T) (x : HeatCircle) : Process (E := Both RealHaarInput) 𝓕 μ H :=
  TwoChannelItoRows.block 𝓕 μ H
    (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
      (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x)
    (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
      (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient hT x)

include hIJ₀ hIJ₁ in
theorem observation (t : ℝ≥0) (ht : t≤H) {T : ℝ} (hT : (t:ℝ)<T) (x : HeatCircle) :
    (fun ω => functional (T-(t:ℝ)) x (S.first t ω))=ᵐ[μ]
      fun ω => functional T x u₀+J.integral (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S t hT x) ω := by
  have h₀ := observe_terminal_integral I₀ (leftIntegral 𝓕 μ H J) hIJ₀ hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x
    (S.additiveInput t) (S.additive_kernel t ht)
  have h₁ := observe_terminal_integral I₁ (rightIntegral 𝓕 μ H J) hIJ₁ hell
    (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient hT x
    (S.residualInput t) (S.residual_kernel t ht)
  have he := TwoChannelItoRows.integral_block 𝓕 μ H J
    (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
      (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x)
    (NativeObservationProcess.process 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
      (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient hT x)
  have heAE := Lp.coeFn_add
    ((leftIntegral 𝓕 μ H J).integral (NativeObservationProcess.process 𝓕 μ H hκ hκ.le
      (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hT x))
    ((rightIntegral 𝓕 μ H J).integral (NativeObservationProcess.process 𝓕 μ H hell
      (hell.le.trans ((hb 0).1.trans (hb 0).2))
      (ContinuousHeatMild.coefficientFunction ha hell hb S.first) S.first_coefficient hT x))
  filter_upwards [S.first_mild t ht,h₀,h₁,heAE] with ω hU h₀ h₁ heAE
  rw [hU,map_add,map_add,functional_heat (τ := T-(t:ℝ)) (t := (t:ℝ))
    (sub_pos.mpr hT) (show 0≤(t:ℝ) from t.2),
    show T-(t:ℝ)+(t:ℝ)=T by ring,h₀,h₁]
  change _=functional T x u₀+J.integral (TwoChannelItoRows.block 𝓕 μ H _ _) ω
  rw [he,heAE]
  simp only [Pi.add_apply]
  ring

end SHE.NativePairObservedFirst
