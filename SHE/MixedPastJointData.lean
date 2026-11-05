module

public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
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

namespace SHE.MixedPastJointData
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastJointData_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastJointData_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastJointData_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastJointData_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastJointData_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastJointData_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedPastJointData_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastJointData_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}

def pastU (v : ℝ≥0) (ω : Ω) : CircleL2 := embed (S.first v ω)
def pastD (v : ℝ≥0) (ω : Ω) : CircleL2 := embed (S.second v ω-S.first v ω)

theorem pastU_measurable (v : ℝ≥0) :
    Measurable[𝓕 v] (pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) :=
  embed.continuous.measurable.comp
    ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable

theorem pastD_measurable (v : ℝ≥0) :
    Measurable[𝓕 v] (pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) :=
  embed.continuous.measurable.comp
    (((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).sub
      ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v)).measurable

/-- Literal joint current observations expressed in relative reference
ages. Stops and targets need not agree for original root observations. -/
def mean (v q : ℝ≥0) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (ω : Ω) : GaussianIncrement.State n :=
  WithLp.toLp 2 (fun i=>MixedNativePastThetaCentering.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S θ (σ i+(v:ℝ)) q (target i+(v:ℝ)) (center i) ω)

theorem mean_measurable (v q : ℝ≥0) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) :
    Measurable (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center) := by
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  exact (MixedNativePastThetaCentering.baseline_stronglyMeasurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ (σ i+(v:ℝ)) q (target i+(v:ℝ)) (center i)).measurable.mono (𝓕.le q) le_rfl

theorem native_offset_eq (v q : ℝ≥0) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (i : Fin n) (hnative : σ i=target i) (ω : Ω) :
    mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center ω i-
      ControlledProfile.mean Λ
        (pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) (θ,(target i,center i))=
      MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q
        (target i+(v:ℝ)) (center i) ω := by
  simp only [mean,MixedNativePastThetaMoments.offset,pastU,pastD,add_sub_cancel_right,hnative]

include hIJ₀ hIJ₁ in
/-- Actual random-reference native offsets have the ORIGINAL relative
full-age gain on every past event. The local q-v moment is compared to
that same original age; no reduced covariance baseline replaces it. -/
theorem native_leaf_moment_on_past_event (hlocal : StandardTerminalPastLocality J)
    (hΛ : 0≤Λ) (hθ : |θ|≤1) (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H)
    (hspan : (q:ℝ)-(v:ℝ)≤1) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (i : Fin n) (hnative : σ i=target i) (hage : 0<target i) (hgap : (q:ℝ)-(v:ℝ)<target i)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    let off := fun ω=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center ω i-
      ControlledProfile.mean Λ
        (pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) (θ,(target i,center i))
    Integrable (fun ω=>|off ω|^(((2*p:ℕ):ℝ)*β)) (μ.restrict A) ∧
      (∫ ω in A,|off ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(target i)^((p:ℝ)*β/2)*μ.real A := by
  intro off
  have hh := MixedNativePastThetaMoments.fractional_moment_on_past_event 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ hlocal hΛ hθ v q hvq hqH hspan (by linarith : (q:ℝ)<target i+(v:ℝ))
    (center i) p hp B hBDG A hA hβ hβ1
  have he : off=MixedNativePastThetaMoments.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q
      (target i+(v:ℝ)) (center i) := funext (native_offset_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center i hnative)
  rw [he]
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg _ _)
  · exact Real.rpow_le_rpow (sub_nonneg.mpr (by exact_mod_cast hvq)) hgap.le (by positivity)
  · have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
    unfold NativeHybridMoments.momentConstant
    exact mul_nonneg B.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)

end SHE.MixedPastJointData
