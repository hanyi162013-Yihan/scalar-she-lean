module

public import SHE.RandomFutureInputEnergy
public import SHE.MixedPastJointData
public import SHE.MixedHilbertInputMoments
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastScoreEnergy
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

variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open AddCircle Real ControlledOldIntervals MeasurableGaussianScores ControlledResidualScoreInput
  ProfileL2 ProfilePointwise ProfileStability
variable (v : ℝ≥0)
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

include hIJ₀ hIJ₁ in
/-- The exact random-past score mass occurring in the actual complete
covariance word has genuine joint sample/output energy with its sharp
time gain. All actual solution, profile and residual applicability is
derived; the original past L2 energy stays inside the bound. -/
theorem actual_score_mass_energy (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast) :
    ∀ᵐ θ ∂volume,∀ q : ℝ,0≤q→
      ∀ (r : ℕ) (lo hi : Fin r→ℝ),
      (∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)→
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i-q≤1)→(∀ i,σ i≤target i)→
      ∀ a : ℝ,q<a→(∀ i,a≤σ i)→
      let mass := fun z : Ω×HeatCircle=>∫ p,
        |ControlledProfile.derivative P Λ (U z.1) (Dir z.1) (p,θ)| *scoreVariance
          (ControlledFixedReserve.covariance P Λ (U z.1) (Dir z.1)
            (fixedProfile P Λ (U z.1) (Dir z.1) lo hi) σ target (fun i=>center i+z.2) q θ)
          (StoppedGaussianFeatures.stoppedRow σ target (fun i=>center i+z.2) p)
            ∂StoppedGaussianFeatures.historyMeasure q
      let C := ControlledProfile.sharpUnit P*(((n:ℝ)/(P.lower/2))*((a-q)/2)^((P.exponent-1)/4)*
        (1+2/(((P.exponent-1)/4)+1)))
      Integrable (fun z=>|mass z|^2) (μ.prod haarAddCircle) ∧
        (∫ z,|mass z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hE := MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v hvH hv1 1 (by decide) Bpast hBDGpast
  have hDi : Integrable (fun ω=>‖Dir ω‖^2) μ := by
    simpa only [MixedPastJointData.pastD,embed_norm] using hE.1
  filter_upwards [random_future_energy P hΛ U Dir hU hDir hsmallPoint hsmallL2 μ hDi] with θ hθ
  intro q hq r lo hi hdisjoint n σ target center hσ1 hages a hqa hstop mass C
  let old : Ω×ControlledProfile.Domain→ℝ := fun z=>fixedProfile P Λ (U z.1) (Dir z.1) lo hi z.2
  have ho : Measurable old := VaryingControlledGaussianFields.fixed_profile_measurable P Λ U Dir hU hDir lo hi
  have hob (z : Ω×ControlledProfile.Domain) : 0≤old z ∧ old z≤P.lower/2 :=
    fixedProfile_bounds P Λ (U z.1) (Dir z.1) lo hi hdisjoint z.2
  have hh := hθ q hq old ho hob n σ target center hσ1 hages a hqa hstop
  have hcoeff (ω : Ω) : ControlledFixedReserve.coefficient P Λ (U ω) (Dir ω)
      (fixedProfile P Λ (U ω) (Dir ω) lo hi) θ=
        (fun p=>profile P Λ (U ω) (Dir ω) (θ,p)-fixedProfile P Λ (U ω) (Dir ω) lo hi p) := by
    funext p
    rfl
  simp only [mass,C,ControlledFixedReserve.covariance,hcoeff]
  simpa only [old,futureInput,MixedPastJointData.pastD,embed_norm] using hh

end SHE.MixedPastScoreEnergy
