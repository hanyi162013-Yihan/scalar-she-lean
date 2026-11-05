module

public import SHE.MixedPastJointData

public import SHE.MixedNativePastThetaMoments
public import SHE.MixedNativeEndpointLimit
public import SHE.ConditionalFatouMoment
public import SHE.MixedNativeEndpointFields
public import SHE.PastEventWeights
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

namespace SHE.MixedPastTerminalData
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastTerminalData_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastTerminalData_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastTerminalData_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastTerminalData_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastTerminalData_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastTerminalData_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open Filter Topology AddCircle
local instance mixedPastTerminalData_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {n : ℕ}
open GaussianIncrement PhysicalProfile

/-- The newest coordinate is a genuine physical point. Older coordinates
remain their literal positive-age joint observations. -/
def mean (θ : ℝ) (v q : ℝ≥0) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (x : HeatCircle) (ω : Ω) : State (n+1) :=
  WithLp.toLp 2 (Fin.cons
    (PredictableScalarField.wordField (Function.uncurry S.first) ω ((q:ℝ),x)+
      θ*(PredictableScalarField.wordField (Function.uncurry S.second) ω ((q:ℝ),x)-
        PredictableScalarField.wordField (Function.uncurry S.first) ω ((q:ℝ),x)))
    (fun i=>MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      θ v q σ target center ω i))

theorem mean_measurable (θ : ℝ) (v q : ℝ≥0) (σ target : Fin n→ℝ)
    (center : Fin n→HeatCircle) (x : HeatCircle) :
    Measurable (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center x) := by
  apply (WithLp.measurable_toLp 2 (Fin (n+1)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · have harg : Measurable (fun ω : Ω=>(ω,((q:ℝ),x))) := measurable_id.prodMk measurable_const
    have hU := (PredictableScalarField.wordField_measurable 𝓕 S.first_predictable).comp harg
    have hV := (PredictableScalarField.wordField_measurable 𝓕 S.second_predictable).comp harg
    exact hU.add (measurable_const.mul (hV.sub hU))
  · exact (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable.comp
      (MixedPastJointData.mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center)

omit [IsProbabilityMeasure μ] in
theorem offset_zero (θ : ℝ) (v q : ℝ≥0) (σ target : Fin n→ℝ)
    (center : Fin n→HeatCircle) (x : HeatCircle) (ω : Ω) :
    mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center x ω 0-
      ControlledProfile.mean Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω))
        (θ,((q:ℝ)-(v:ℝ),x))=
      MixedNativeEndpointLimit.offset 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q x ω := rfl

include hIJ₀ hIJ₁ in
/-- At the true remainder endpoint, the newest coordinate and every
older native leaf satisfy one original-age conditional offset packet.
The spatial event is common to ALL past events and ALL leaf indices. -/
theorem native_offsets_on_past_event (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    {θ : ℝ} (hθ : |θ|≤1) (v q : ℝ≥0) (hvq : v<q) (hqH : q≤H)
    (hspan : (q:ℝ)-(v:ℝ)≤1) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ i : Fin (n+1),
      (Fin.cons ((q:ℝ)-(v:ℝ)) σ : Fin (n+1)→ℝ) i=(Fin.cons ((q:ℝ)-(v:ℝ)) target : Fin (n+1)→ℝ) i →
      ∀ A : Set Ω,MeasurableSet[𝓕 v] A →
      let off := fun ω=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        θ v q σ target center x ω i-
          ControlledProfile.mean Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω))
            (θ,((Fin.cons ((q:ℝ)-(v:ℝ)) target : Fin (n+1)→ℝ) i,(Fin.cons x center : Fin (n+1)→HeatCircle) i))
      Integrable (fun ω=>|off ω|^(((2*p:ℕ):ℝ)*β)) (μ.restrict A) ∧
        (∫ ω in A,|off ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
          (NativeHybridMoments.momentConstant p B κ M)^β*
            ((Fin.cons ((q:ℝ)-(v:ℝ)) target : Fin (n+1)→ℝ) i)^((p:ℝ)*β/2)*μ.real A := by
  have hend := MixedNativeEndpointMoments.fractional_moment_on_past_event
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hlocal hΛ hθ v q hvq hqH hspan p hp B hBDG hβ hβ1
  filter_upwards [hend] with x hx
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · intro _ A hA
    simpa only [Fin.cons_zero,offset_zero] using hx A hA
  · intro hnative A hA
    simp only [Fin.cons_succ] at hnative ⊢
    have hh := MixedPastJointData.native_leaf_moment_on_past_event
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ hlocal hΛ hθ
      v q hvq.le hqH hspan σ target center j hnative
      (lt_of_le_of_lt (sub_nonneg.mpr (by exact_mod_cast hvq.le)) (hgap j)) (hgap j)
      p hp B hBDG hβ hβ1 A hA
    exact hh

end SHE.MixedPastTerminalData
