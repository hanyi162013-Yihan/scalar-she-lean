module

public import SHE.MixedPastTerminalCovarianceMoments
public import SHE.MixedPastConvexScoreMass
public import SHE.BoundedVaryingCovarianceInput
public import SHE.FullResidualFrameRange
public import SHE.StoppedCovarianceInput
public import SHE.PointwiseCompleteGaussianWord
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedPastJointData
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

namespace SHE.MixedPastTerminalConvexCovariance
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCompleteOffsetWeights_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCompleteOffsetWeights_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCompleteOffsetWeights_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCompleteOffsetWeights_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCompleteOffsetWeights_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCompleteOffsetWeights_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

open PastItoInputs PastItoAlgebra PhysicalProfile AddCircle

variable (θ : ℝ)

local instance mixedPastCompleteOffsetWeights_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCompleteOffsetWeights_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

include hIJ₀ hIJ₁ in
/-- The actual complete terminal covariance word for a FINITE endpoint
profile difference and its real convex future law. Past-mass measurability,
ALL required moment integrability and the newest native offset packet are
derived from the original stochastic pair. The true mass remains in the
bound, ready for the sharp joint spatial energy estimate. -/
theorem input_moment (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v<q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (leaf : Fin m→Fin (n+1))
    (hnative : ∀ j,(Fin.cons ((q:ℝ)-(v:ℝ)) σ : Fin (n+1)→ℝ) (leaf j)=
      (Fin.cons ((q:ℝ)-(v:ℝ)) target : Fin (n+1)→ℝ) (leaf j))
    (ht : ∀ j,(Fin.cons ((q:ℝ)-(v:ℝ)) target : Fin (n+1)→ℝ) (leaf j)∈Set.Ioc 0 P.horizon)
    (b : ℕ) (hb : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (θ0 θ1 : ℝ) {ζ : ℝ} (hζ : 0≤ζ) (hζ1 : ζ≤1) :
    let sgm : Fin (n+1)→ℝ := Fin.cons ((q:ℝ)-(v:ℝ)) σ
    let T : Fin (n+1)→ℝ := Fin.cons ((q:ℝ)-(v:ℝ)) target
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      let C : Fin (n+1)→HeatCircle := Fin.cons x center
      ∀ (lo hi : Fin r→ℝ), (∀ j,(q:ℝ)-(v:ℝ)≤lo j) → (∀ j,lo j<hi j) →
      (∀ j i,sgm i≤lo j ∨ hi j≤sgm i) → (∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j) →
      let c : Ω×StoppedGaussianFeatures.Domain→ℝ := fun z=>
        BoundedWindowDecomposition.convexProfile P Λ (U v z.1) (Dir v z.1) θ0 θ1 ζ z.2
      let e : Ω×StoppedGaussianFeatures.Domain→ℝ := fun z=>
        ControlledProfile.profile P Λ (U v z.1) (Dir v z.1) (θ0,z.2)-
          ControlledProfile.profile P Λ (U v z.1) (Dir v z.1) (θ1,z.2)
      ∀ D : Fin r→State (n+1),
      (∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (familyCovariance sgm T C (referenceProfile P Λ (U v ω) (Dir v ω)) lo hi j)).range) →
      ∀ (g : Fin 1→Fin (n+1)) (F : State 1→ℝ),Measurable F →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν → ContDiff ℝ r F →
      (∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j) →
      ∀ K : ℝ,0≤K →
      (∀ ω,|∏ j,scoreVariance
        (familyCovariance sgm T C (referenceProfile P Λ (U v ω) (Dir v ω)) lo hi j) (D j)|≤K) →
      let B := fun ω=>StoppedGaussianFeatures.stoppedCovariance sgm T C
        (BoundedWindowDecomposition.residual P Λ (U v ω) (Dir v ω) lo hi (fun z=>c (ω,z)))
          ((q:ℝ)-(v:ℝ))
      let row := StoppedGaussianFeatures.stoppedRow sgm T C
      let mass := fun ω=>∫ z,|e (ω,z)| *scoreVariance (B ω) (row z)
        ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))
      let mean := MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center x
      let G := fun ω=>(1/2:ℝ)*∫ z,e (ω,z)*BoundedCompleteGaussianWord.value P Λ (U v ω) (Dir v ω)
        (fun z=>c (ω,z)) θ ((q:ℝ)-(v:ℝ)) sgm T C lo hi (mean ω) true D (row z) g leaf F
          ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))
      Integrable (fun ω=>|G ω|^(2*b)) μ ∧ (∫ ω,|G ω|^(2*b) ∂μ)≤
        MixedPastWordMoments.momentConstant P r m b
          ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
        (K*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>T (leaf j)) A0 ν/2)^(2*b)*
          (∫ ω,(mass ω)^(2*b) ∂μ) := by
  intro sgm T
  filter_upwards [MixedPastTerminalCovarianceMoments.input_moment (r:=r)
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspan σ target center hσ hσ1 hages hgap leaf hnative ht b hb B0 hBDG] with x hx
  intro C lo hi hlo hlohi hstop hdisjoint c e D hD g F hFm A0 ν hA0 hν hf hfb K hK hgeom
    B row mass mean G
  have hu := (MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd := (MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hc : Measurable c := BoundedResidualFields.convexProfile_measurable P Λ θ0 θ1 ζ _ _ hu hd
  have hcb (ω z) : P.lower≤c (ω,z) ∧ c (ω,z)≤P.upper :=
    BoundedWindowDecomposition.convexProfile_bounds P Λ (U v ω) (Dir v ω) θ0 θ1 hζ hζ1 z
  have he : Measurable e := (VaryingControlledGaussianFields.profile_measurable P Λ θ0 _ _ hu hd).sub
    (VaryingControlledGaussianFields.profile_measurable P Λ θ1 _ _ hu hd)
  have hcoarse (ω z) : |e (ω,z)|≤2*P.upper := by
    have h0 := ControlledProfile.profile_bounds P Λ (U v ω) (Dir v ω) (θ0,z)
    have h1 := ControlledProfile.profile_bounds P Λ (U v ω) (Dir v ω) (θ1,z)
    have hb0 : |ControlledProfile.profile P Λ (U v ω) (Dir v ω) (θ0,z)|≤P.upper := by
      rw [abs_of_nonneg (P.lower_pos.le.trans h0.1)]; exact h0.2
    have hb1 : |ControlledProfile.profile P Λ (U v ω) (Dir v ω) (θ1,z)|≤P.upper := by
      rw [abs_of_nonneg (P.lower_pos.le.trans h1.1)]; exact h1.2
    have hh := abs_sub_le (ControlledProfile.profile P Λ (U v ω) (Dir v ω) (θ0,z)) 0
      (ControlledProfile.profile P Λ (U v ω) (Dir v ω) (θ1,z))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    exact hh.trans ((add_le_add hb0 hb1).trans_eq (by ring))
  have hq0 : 0<(q:ℝ)-(v:ℝ) := sub_pos.mpr (by exact_mod_cast hvq)
  have hsgmT (i) : sgm i≤T i := Fin.cases le_rfl hages i
  have hm := MixedPastConvexScoreMass.past_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v sgm T C
      ((q:ℝ)-(v:ℝ)) lo hi θ0 θ1 ζ
  have hmi := MixedPastConvexScoreMass.power_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v sgm T C hsgmT
      ((q:ℝ)-(v:ℝ)) lo hi hdisjoint θ0 θ1 hζ hζ1 (2*b)
  exact hx lo hi hlo hlohi hstop hdisjoint c hc hcb D hD g F hFm A0 ν hA0 hν hf hfb
    e he (2*P.upper) hcoarse K hK hgeom (hm.pow_const (2*b)) hmi

end SHE.MixedPastTerminalConvexCovariance
