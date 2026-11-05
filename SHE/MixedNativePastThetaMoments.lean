module

public import SHE.MixedNativePastThetaCentering
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
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

namespace SHE.MixedNativePastThetaMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativePastThetaMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativePastThetaMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativePastThetaMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativePastThetaMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativePastThetaMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativePastThetaMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

open PastItoInputs PastItoAlgebra PhysicalProfile

variable (θ : ℝ)

/-- Actual native joint leaf offset from the controlled profile whose
initial states are the real random U_v and V_v-U_v. -/
def offset (v q : ℝ≥0) (T : ℝ) (x : HeatCircle) (ω : Ω) : ℝ :=
  MixedNativePastThetaCentering.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ T q T x ω-
    ControlledProfile.mean Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω)) (θ,(T-(v:ℝ),x))

include hIJ₀ hIJ₁ in
/-- Genuine conditional random-past rough-leaf moment, with its exact
past-event mass and local duration q-v. The only extra stochastic
component is ordinary block1 event pullout for the existing full-H J;
BDG is the SAME unconditional accepted block3. -/
theorem fractional_moment_on_past_event (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ₀ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω => |offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x ω|^(((2*p:ℕ):ℝ)*β)) (μ.restrict A) ∧
      (∫ ω in A,|offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (NativeHybridMoments.momentConstant p B κ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2)*μ.real A := by
  obtain ⟨hθ,hcenter⟩ := MixedNativePastThetaCentering.centered_current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ θ hΛ hθ₀ v q hvq hqH hT.le hT x
  have hh := NativePastHybridMoments.fractional_moment_on_past_event 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient v q hT x hΛ hθ J hlocal hvq hqH hspan p hp B hBDG A hA hβ hβ1
  have hTv : (v:ℝ)<T := lt_of_le_of_lt (by exact_mod_cast hvq) hT
  have he : (fun ω => offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x ω)=ᵐ[μ]
      (NativePastHybridMoments.value 𝓕 μ H hκ hκ.le
        (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
        hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
        (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
        S.first_coefficient S.second_coefficient v q hT x hΛ hθ J) := by
    filter_upwards [hcenter] with ω hω
    rw [offset,← MixedNativePastThetaCentering.baseline_eq_profile 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v hTv x ω]
    exact hω
  have he' : (fun ω => |offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q T x ω|^(((2*p:ℕ):ℝ)*β))=ᵐ[μ.restrict A]
      (fun ω => |NativePastHybridMoments.value 𝓕 μ H hκ hκ.le
        (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
        hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
        (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
        S.first_coefficient S.second_coefficient v q hT x hΛ hθ J ω|^(((2*p:ℕ):ℝ)*β)) := by
    filter_upwards [ae_restrict_of_ae he] with ω hω
    rw [hω]
  exact ⟨hh.1.congr he'.symm,(integral_congr_ae he').trans_le hh.2⟩

end SHE.MixedNativePastThetaMoments
