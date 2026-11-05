module

public import SHE.MixedPastReferenceInput
public import SHE.PastReferenceStopped
public import SHE.PastReferenceIntegral
public import SHE.MixedHilbertInputMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastReferenceStopped
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open MixedPastReference
open scoped NNReal ENNReal
local instance mixedPastReferenceStopped_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastReferenceStopped_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedPastReferenceStopped_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedPastReferenceStopped_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastReferenceStopped_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedPastReferenceStopped_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastReferenceStopped_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedPastReferenceStopped_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastReferenceStopped_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastReferenceStopped_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastReferenceStopped_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedPastReferenceStopped_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ) (hκP : κ<P.lower)
variable (θ η : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hv1 : (v:ℝ)≤1)
variable (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
variable (p : ℕ) (hp : 0<p) (Bpast : ℝ≥0)
variable (hBDGpast : StandardTerminalBDGPower (2*p) J Bpast)

local notation "Input"=>MixedPastReference.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
  P hΛ hκP θ η hsmall v b hvb hbH hv1 hsmallTime p hp Bpast hBDGpast

/-- Partial frozen observation on the SAME original driver and full
terminal heat target b. Only the input support is stopped at s. -/
def input (s : ℝ) : Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H :=
  StoppedItoInputs.stop 𝓕 μ H s Input

local notation "Partial"=>input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
  P hΛ hκP θ η hsmall v b hvb hbH hv1 hsmallTime p hp Bpast hBDGpast

include hIJ₀ hIJ₁ in
/-- Actual conditional partial-time frozen-reference difference moment.
The deterministic final heat target is b, so the gain is (b-v)^(beta/2)
in its bracket; current s only stops the genuine original Ito input. -/
theorem actual_moment (hlocal : StandardTerminalPastLocality I₁)
    (s : ℝ) (Bnext : ℝ≥0) (hBDGnext : StandardTerminalBDGPower p I₁ Bnext)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    Integrable (fun ω=>‖I₁.integral (Partial s) ω‖^(2*p)) (μ.restrict A) ∧
      (∫ ω in A,‖I₁.integral (Partial s) ω‖^(2*p) ∂μ)≤
        (Bnext:ℝ)*PastReferenceBracket.energyConstant P κ θ η ((b:ℝ)-(v:ℝ))^p*
          (∫ ω in A,‖S.second v ω-S.first v ω‖^(2*p) ∂μ) := by
  have hd:=MixedPastReference.data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    hΛ v (hvb.le.trans hbH) hv1 hp Bpast hBDGpast
  have hh:=PastReferenceStopped.moment_on_past_event
    𝓕 μ P hΛ hκP θ η hsmall H v b hvb hbH hsmallTime
    (MixedPastReference.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)
    (MixedPastReference.data_past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)
    hd.1 s I₁ hlocal hp Bnext hBDGnext hd.2 A hA
  simpa only [input,MixedPastReference.input,PastReferenceStopped.stopped,MixedPastReference.data,embed_norm] using hh

end SHE.MixedPastReferenceStopped
