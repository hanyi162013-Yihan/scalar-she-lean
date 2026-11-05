module

public import SHE.MixedNativePastIncrement
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativePastHybridIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativePastHybridIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativePastHybridIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativePastHybridIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativePastHybridIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativePastHybridIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativePastHybridIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

open PastItoInputs PastItoAlgebra
local notation "Rows" => MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "N" => MixedNativePairScaledMartingale.normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

def input (v q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ}
    (hΛ : 0≤Λ) (hθ : |θ|≤1) : Process (E := Both RealHaarInput) 𝓕 μ H :=
  post 𝓕 μ H v (NativeHybridInput.input 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ)

include hIJ₀ hIJ₁ in
/-- Actual observed hybrid displacement from its random past-state
baseline. Every noise term is restricted inside the original full-H J. -/
theorem centered_increment (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ} (hΛ : 0≤Λ) (hθ : |θ|≤1) :
    (fun ω => functional (T-(q:ℝ)) x (S.first q ω)+θ*functional (T-(q:ℝ)) x (S.second q ω-S.first q ω)-
      (functional (T-(v:ℝ)) x (S.first v ω)+θ*Real.exp (-Λ*((q:ℝ)-(v:ℝ)))*
        functional (T-(v:ℝ)) x (S.second v ω-S.first v ω)))=ᵐ[μ]
      J.integral (input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v q hT x hΛ hθ) := by
  have he := PastHybridIntegral.integral_eq 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient v q hT x hΛ hθ J
  change J.integral (input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v q hT x hΛ hθ)=
    J.integral (post 𝓕 μ H v (Rows q hT x))+θ • (rightIntegral 𝓕 μ H J).integral (post 𝓕 μ H v (N hΛ q hT x)) at he
  filter_upwards [MixedNativePastIncrement.first_increment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ v q hvq hqH hT x,
    MixedNativePastIncrement.difference_increment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      J hIJ₀ hIJ₁ hΛ v q hvq hqH hT x,
    Lp.coeFn_add (J.integral (post 𝓕 μ H v (Rows q hT x)))
      (θ • (rightIntegral 𝓕 μ H J).integral (post 𝓕 μ H v (N hΛ q hT x))),
    Lp.coeFn_smul θ ((rightIntegral 𝓕 μ H J).integral (post 𝓕 μ H v (N hΛ q hT x)))] with ω hU hD ha hs
  have hi := congrArg (fun z : Lp ℝ 2 μ => z ω) he
  rw [ha] at hi
  simp only [Pi.add_apply] at hi
  rw [hs] at hi
  simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul] at hi
  rw [hi,← hU,← hD]
  ring

end SHE.MixedNativePastHybridIdentity
