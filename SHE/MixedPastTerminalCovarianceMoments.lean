module

public import SHE.MixedPastTerminalCompleteWeights
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

namespace SHE.MixedPastTerminalCovarianceMoments
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
/-- The COMPLETE actual terminal covariance-input word, including its
physical newest leaf. One spatial event works for every bounded elliptic
intermediate law and every signed bounded past input. Gaussian ranges
and continuum integrability are derived; the quantitative bound retains
the true conditional input mass, without a spatial supremum. -/
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
    (b : ℕ) (hb : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0) :
    let sgm : Fin (n+1)→ℝ := Fin.cons ((q:ℝ)-(v:ℝ)) σ
    let T : Fin (n+1)→ℝ := Fin.cons ((q:ℝ)-(v:ℝ)) target
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      let C : Fin (n+1)→HeatCircle := Fin.cons x center
      ∀ (lo hi : Fin r→ℝ), (∀ j,(q:ℝ)-(v:ℝ)≤lo j) → (∀ j,lo j<hi j) →
      (∀ j i,sgm i≤lo j ∨ hi j≤sgm i) → (∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j) →
      ∀ (c : Ω×StoppedGaussianFeatures.Domain→ℝ),Measurable c →
      (∀ ω z,P.lower≤c (ω,z) ∧ c (ω,z)≤P.upper) →
      ∀ D : Fin r→State (n+1),
      (∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (familyCovariance sgm T C (referenceProfile P Λ (U v ω) (Dir v ω)) lo hi j)).range) →
      ∀ (g : Fin 1→Fin (n+1)) (F : State 1→ℝ),Measurable F →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν → ContDiff ℝ r F →
      (∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j) →
      ∀ (e : Ω×StoppedGaussianFeatures.Domain→ℝ),Measurable e →
      ∀ Ecoarse : ℝ,(∀ ω z,|e (ω,z)|≤Ecoarse) →
      ∀ K : ℝ,0≤K →
      (∀ ω,|∏ j,scoreVariance
        (familyCovariance sgm T C (referenceProfile P Λ (U v ω) (Dir v ω)) lo hi j) (D j)|≤K) →
      let B := fun ω=>StoppedGaussianFeatures.stoppedCovariance sgm T C
        (BoundedWindowDecomposition.residual P Λ (U v ω) (Dir v ω) lo hi (fun z=>c (ω,z)))
          ((q:ℝ)-(v:ℝ))
      let row := StoppedGaussianFeatures.stoppedRow sgm T C
      let mass := fun ω=>∫ z,|e (ω,z)| *scoreVariance (B ω) (row z)
        ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))
      Measurable[𝓕 v] (fun ω=>(mass ω)^(2*b)) → Integrable (fun ω=>(mass ω)^(2*b)) μ →
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
  filter_upwards [MixedPastTerminalCompleteWeights.constant_with_past_weight (r:=r)
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspan σ target center hgap leaf hnative b hb B0 hBDG] with x hx
  intro C lo hi hlo hlohi hstop hdisjoint c hc hcb D hD g F hFm A0 ν hA0 hν hf hfb
    e he Ecoarse hcoarse K hK hgeom B row mass hmass hmassI mean G
  have hq0 : 0<(q:ℝ)-(v:ℝ) := sub_pos.mpr (by exact_mod_cast hvq)
  have hsgm (i) : 0<sgm i := Fin.cases hq0 hσ i
  have hsgm1 (i) : sgm i≤1 := Fin.cases hspan hσ1 i
  have hsgmT (i) : sgm i≤T i := Fin.cases le_rfl hages i
  have hu : Measurable (U v) := (MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd : Measurable (Dir v) := (MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm := MixedPastTerminalData.mean_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center x
  have hres (ω) : Measurable (BoundedWindowDecomposition.residual P Λ (U v ω) (Dir v ω)
      lo hi (fun z=>c (ω,z))) :=
    BoundedWindowDecomposition.residual_measurable P Λ (U v ω) (Dir v ω) lo hi _
      (hc.comp (measurable_const.prodMk measurable_id))
  have hresb (ω z) := BoundedWindowDecomposition.residual_bounds
    P Λ (U v ω) (Dir v ω) lo hi hdisjoint (fun z=>c (ω,z)) (hcb ω) z
  have hrange (ω) : ∀ᵐ z ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ)),
      row z∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (B ω)).range := by
    have hh := FullResidualFrameRange.row_mem_all_ranges_ae sgm T C hsgmT ((q:ℝ)-(v:ℝ))
      (fun _ : Unit=>BoundedWindowDecomposition.residual P Λ (U v ω) (Dir v ω) lo hi (fun z=>c (ω,z)))
      (fun _=>hres ω) (half_pos P.lower_pos) (fun _=>hresb ω)
    exact hh.mono (fun _ hz=>hz ())
  have hrow : Measurable row := StoppedGaussianFeatures.stoppedRow_measurable sgm T C
  have hEnergy (ω) : Integrable (fun z=>|e (ω,z)| *scoreVariance (B ω) (row z))
      (StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))) := by
    have heω : Measurable (fun z=>e (ω,z)) := he.comp (measurable_const.prodMk measurable_id)
    have hi := StoppedCovarianceInput.weighted_input_energy_integrable sgm T C hsgm hsgm1 hsgmT
      (fun z=>e (ω,z)) heω (by norm_num : -1<(0:ℝ))
      (fun z _=>by simpa only [Real.rpow_zero,mul_one] using hcoarse ω z)
    have hi' := hi.mono_measure (StoppedRowWeighted.historyMeasure_mono hq0.le)
    exact GaussianWordCovarianceBound.scoreEnergy_outer_integrable
      (StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))) (B ω) row hrow (fun z=>e (ω,z)) heω hi'
  have hw := hx (fun ω=>(mass ω)^(2*b)) hmass
    (fun ω=>(even_two_mul b).pow_nonneg (mass ω)) hmassI
  exact BoundedVaryingCovarianceInput.input_moment μ
    (StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))) P Λ (U v) (Dir v) hu hd c hc hcb θ
    ((q:ℝ)-(v:ℝ)) hq0.le sgm T C hsgm hsgm1 hsgmT lo hi hlo hlohi hstop hdisjoint mean hm D hD
    row hrow hrange g leaf hnative ht F hFm hA0 hν hf hfb b hb e he hEnergy
    K (MixedPastWordMoments.momentConstant P r m b
      ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)) hK hgeom hw.1 hw.2

end SHE.MixedPastTerminalCovarianceMoments
