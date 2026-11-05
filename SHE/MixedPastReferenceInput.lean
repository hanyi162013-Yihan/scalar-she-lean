module

public import SHE.PastReferenceIntegral
public import SHE.MixedHilbertInputMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastReference
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

/-- The actual random initial data used by the frozen reference at v.
The difference convention here is V-U. -/
def data (v : ℝ≥0) (ω : Ω) : Inputs :=
  (embed (S.first v ω),embed (S.second v ω-S.first v ω))

theorem data_past_measurable (v : ℝ≥0) :
    Measurable[𝓕 v] (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v) := by
  have hU : StronglyMeasurable[𝓕 v] (S.first v) :=
    (show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v
  have hV : StronglyMeasurable[𝓕 v] (S.second v) :=
    (show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v
  exact (embed.continuous.measurable.comp hU.measurable).prodMk
    (embed.continuous.measurable.comp (hV.sub hU).measurable)

variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- All moments needed for the reference input follow from the actual
mixed solution. They are not extra assumptions about a frozen process. -/
theorem data_moments (hΛ : 0≤Λ) (v : ℝ≥0) (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    {p : ℕ} (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower (2*p) J B) :
    Integrable (fun ω => ‖(data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v ω).2‖^2) μ ∧
    Integrable (fun ω => ‖(data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v ω).2‖^(2*p)) μ := by
  have hm := MixedHeatedDifferenceMoments.current_four_moment 𝓕 μ H Λ κ hκ haU haV hell
    hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v hvH hv1 p hp B hBDG
  have hs : AEStronglyMeasurable (fun ω => S.second v ω-S.first v ω) μ :=
    (MixedHeatedDifferenceMoments.difference_measurable 𝓕 μ H Λ κ hκ haU haV
    hell hbU hbV I₀ I₁ u₀ S v).aestronglyMeasurable
  have h2 := integrable_norm_pow_of_le hs (show 2≤4*p by omega) hm.1
  have hp2 := integrable_norm_pow_of_le hs (show 2*p≤4*p by omega) hm.1
  simpa only [data,embed_norm] using And.intro h2 hp2

variable (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ) (hκP : κ<P.lower)
variable (θ η : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hv1 : (v:ℝ)≤1)
variable (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
variable (p : ℕ) (hp : 0<p) (Bpast : ℝ≥0)
variable (hBDGpast : StandardTerminalBDGPower (2*p) J Bpast)

/-- Actual frozen signed residual input, based on the actual pair at v.
Predictability and finite energy are both derived internally. -/
def input : Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H :=
  PastReferenceBracket.input 𝓕 μ P hΛ hκP θ η hsmall H v b hvb hbH hsmallTime
    (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)
    (data_past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)
    (data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      hΛ v (hvb.le.trans hbH) hv1 hp Bpast hBDGpast).1

include hIJ₀ hIJ₁ in
/-- Conditional every-even-order moment of the original residual-channel
integral, with every frozen-reference applicability hypothesis discharged
by the actual mixed solution and the standard stochastic packages. -/
theorem actual_moment (hlocal : StandardTerminalPastLocality I₁)
    (Bnext : ℝ≥0) (hBDGnext : StandardTerminalBDGPower p I₁ Bnext)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    let R := input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
      P hΛ hκP θ η hsmall v b hvb hbH hv1 hsmallTime p hp Bpast hBDGpast
    Integrable (fun ω => ‖I₁.integral R ω‖^(2*p)) (μ.restrict A) ∧
      (∫ ω in A,‖I₁.integral R ω‖^(2*p) ∂μ)≤
        (Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η ((b:ℝ)-(v:ℝ))^p*
          (∫ ω in A,‖S.second v ω-S.first v ω‖^(2*p) ∂μ) := by
  have hd := data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ v (hvb.le.trans hbH) hv1 hp Bpast hBDGpast
  have hh := PastReferenceBracket.moment_on_past_event 𝓕 μ P hΛ hκP θ η hsmall H v b
    hvb hbH hsmallTime (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)
    (data_past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)
    hd.1 I₁ hlocal hp Bnext hBDGnext hd.2 A hA
  simpa only [input,data,embed_norm] using hh

end SHE.MixedPastReference
