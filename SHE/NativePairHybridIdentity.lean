module

public import SHE.NativePairResolvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativePairHybridIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairHybridIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairHybridIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairHybridIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairHybridIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairHybridIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairHybridIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

def input (q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle)
    (hΛ : 0≤Λ) {θ : ℝ} (hθ : |θ|≤1) : Process (E := Both RealHaarInput) 𝓕 μ H :=
  NativeHybridInput.input 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ

include hIJ₀ hIJ₁ in
/-- The actual native current interpolation, centered at its current-time
deterministic heat mean, is exactly the full-horizon hybrid scalar Itô
integral. This identifies the moment input with the constructed pair. -/
theorem centered_current (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ} (hθ : |θ|≤1) :
    (fun ω => functional (T-(q:ℝ)) x (S.first q ω+θ • (S.second q ω-S.first q ω))-
      (functional T x u₀+θ*Real.exp (-Λ*(q:ℝ))*functional T x (v₀-u₀)))=ᵐ[μ]
      J.integral (input 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x hΛ hθ) := by
  let D := NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ
  let R := NativePairObservedFirst.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x
  have he := NativeHybridInput.integral_eq 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ J
  change J.integral (input 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x hΛ hθ)=
    J.integral R+θ • (rightIntegral 𝓕 μ H J).integral D at he
  have hadd := Lp.coeFn_add (J.integral R) (θ • (rightIntegral 𝓕 μ H J).integral D)
  rw [← he] at hadd
  filter_upwards [NativePairObservedFirst.observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ q hq hT x,
    NativePairResolvent.difference_observation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq hT x,
    hadd,Lp.coeFn_smul θ ((rightIntegral 𝓕 μ H J).integral D)] with ω hfirst hdiff hadd hsmul
  rw [map_add,map_smul,hfirst,hdiff,hadd]
  change _=J.integral R ω+(θ • (rightIntegral 𝓕 μ H J).integral D) ω
  rw [hsmul]
  change _=J.integral R ω+θ*(rightIntegral 𝓕 μ H J).integral D ω
  ring

end SHE.NativePairHybridIdentity
