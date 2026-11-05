module

public import SHE.EndpointConvexScoreEnergy

public import SHE.RandomFutureInputEnergy
public import SHE.MixedPastJointData
public import SHE.MixedHilbertInputMoments
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastEndpointScoreEnergy
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
/-- Finite endpoint-profile score mass from the ACTUAL random past.
The newest future coordinate is inactive and is projected out exactly.
The sharp bound keeps genuine past solution energy to beta, with no
negative gap power and no extra stochastic input block. -/
theorem actual_endpoint_mass_energy (P:CanonicalCovariance.ProfileParameters) (hΛ:0≤Λ)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH:v≤H) (hv1:(v:ℝ)≤1)
    (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (q:ℝ) (hq:0≤q) (θ η:ℝ) (newCenter:HeatCircle) {ζ:ℝ} (hζ:0≤ζ) (hζ1:ζ≤1)
    {r:ℕ} (lo hi:Fin r→ℝ) (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (n:ℕ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle)
    (hσ1:∀i,σ i-q≤1) (hages:∀i,σ i≤target i)
    (stop:ℝ) (hstop:q<stop) (hstops:∀i,stop≤σ i):
    let c:=fun z:Ω×ControlledProfile.Domain=>BoundedWindowDecomposition.residual P Λ (U z.1) (Dir z.1) lo hi
      (BoundedWindowDecomposition.convexProfile P Λ (U z.1) (Dir z.1) θ η ζ) z.2
    let e:=fun z:Ω×ControlledProfile.Domain=>ControlledProfile.profile P Λ (U z.1) (Dir z.1) (θ,z.2)-
      ControlledProfile.profile P Λ (U z.1) (Dir z.1) (η,z.2)
    let mass:=fun z:Ω×HeatCircle=>ControlledResidualScoreInput.futureInput
      (Fin.cons q σ) (Fin.cons q target) (Fin.cons newCenter center) (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2
    let C:=2*P.holder*|θ-η|^P.exponent*(3*((n:ℝ)/(P.lower/2)))
    Integrable (fun z=>|mass z|^2) (μ.prod haarAddCircle) ∧
      (∫z,|mass z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^P.exponent:=by
  have hU:=(MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir:=(MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hE:=MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v hvH hv1 1 (by decide) Bpast hBDGpast
  have hDi:Integrable (fun ω=>‖Dir ω‖^2) μ:=by
    simpa only [MixedPastJointData.pastD,embed_norm] using hE.1
  have hh:=EndpointConvexScoreEnergy.future_energy P hΛ U Dir hU hDir hsmallL2 μ hDi
    q hq θ η newCenter hζ hζ1 lo hi hdisjoint n σ target center hσ1 hages stop hstop hstops
  simpa only [MixedPastJointData.pastD,embed_norm] using hh

end SHE.MixedPastEndpointScoreEnergy
