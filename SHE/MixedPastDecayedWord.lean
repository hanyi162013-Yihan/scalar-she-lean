module

public import SHE.MixedPastWordMoments
public import SHE.AllDataDecayFreshScore
public import SHE.FiniteAssignmentMoments
public import SHE.MinimumGapChoice
public import SHE.MixedPastAssignedMoments
public import SHE.PastEventWeights
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

namespace SHE.MixedPastDecayedWord
local instance mixedPastDecayedWord_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
open Real AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastDecayedWord_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastDecayedWord_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastDecayedWord_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastDecayedWord_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastDecayedWord_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastDecayedWord_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedPastDecayedWord_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastDecayedWord_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}


include hIJ₀ hIJ₁ in
/-- The actual full random-past assigned word with a true later damped
heat-row first score. Its decay, fresh gap and original parent heat
envelope are proved on one event before all random past-data choices. -/
theorem moment_on_past_event_ae (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0 ≤ Λ) (hθ : |θ| ≤ 1)
    (v q : ℝ≥0) (hvq : v ≤ q) (hqH : q ≤ H) (hspan : (q:ℝ)-(v:ℝ) ≤ 1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i ≤ 1) (hages : ∀ i,σ i ≤ target i)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)-(v:ℝ) ≤ lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i ≤ lo j ∨ hi j ≤ σ i)
    (hdisjoint : ∀ j l,j≠l→hi j ≤ lo l ∨ hi l ≤ lo j)
    (s front : ℝ) (hqs : (q:ℝ)-(v:ℝ)≤s) (hsfront : s<front)
    (hfront : ∀ i,front≤σ i)
    (hsmall : ∀ i,target i-s≤UniformFutureProfileScores.horizon n)
    (D : Fin r→State n)
    (hD : ∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ContDiff ℝ r F)
    (hfb : ∀ j,j ≤ r→∀ z,‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)

    (K : ℝ) (hK : 0 ≤ K)
    (holdScore : ∀ ω,
      ∏ j,scoreVariance
        (familyCovariance σ target center (referenceProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j) (D j) ≤ K) :
    ∀ᵐ y : HeatCircle ∂haarAddCircle,∀ A : Set Ω,MeasurableSet[𝓕 v] A →
    let Z : Fin n→WordRecursion.Observation:=fun i=>⟨σ i,target i,center i⟩
    let E:=StopWeightedRows.weightedHeatRow Λ Z ((q:ℝ)-(v:ℝ)) s y
    let G:=MixedPastWordMoments.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ
      P v q σ target center lo hi false D E g leaf F
    let fresh:=exp (-Λ*(s-((q:ℝ)-(v:ℝ))))*
      sqrt (2*UniformFutureProfileScores.constant n/(P.lower*(front-s)))*
      ∑ i,sqrt ‖ProfileVariance.heatPhysical (4*(target i-s)) (center i) y‖
    Integrable (fun ω=>|G ω|^(2*b)) (μ.restrict A) ∧
      (∫ ω in A,|G ω|^(2*b) ∂μ) ≤ 
        MixedPastWordMoments.momentConstant P r m b
          ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
          (K*fresh*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν)^(2*b)*μ.real A := by
  let Z : Fin n→WordRecursion.Observation:=fun i=>⟨σ i,target i,center i⟩
  let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  let dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hq0 : 0 ≤ (q:ℝ)-(v:ℝ):=sub_nonneg.mpr (by exact_mod_cast hvq)
  filter_upwards [AllDataDecayFreshScore.all_data_decay_ae P Λ hΛ U dir lo hi hdisjoint Z hages
    hq0 hqs hsfront hfront hsmall] with y hy
  intro A hA
  dsimp only
  let E:=StopWeightedRows.weightedHeatRow Λ Z ((q:ℝ)-(v:ℝ)) s y
  let fresh:=exp (-Λ*(s-((q:ℝ)-(v:ℝ))))*
    sqrt (2*UniformFutureProfileScores.constant n/(P.lower*(front-s)))*
      ∑ i,sqrt ‖ProfileVariance.heatPhysical (4*(target i-s)) (center i) y‖
  have hfresh0 : 0 ≤ fresh:=by
    exact mul_nonneg (mul_nonneg (exp_pos _).le (sqrt_nonneg _))
      (Finset.sum_nonneg (fun _ _=>sqrt_nonneg _))
  have hE (ω : Ω):= (hy ω θ).1
  have hscore (ω : Ω) :
      |(∏ j,scoreVariance (familyCovariance σ target center (referenceProfile P Λ (U ω) (dir ω)) lo hi j) (D j))*
        scale false (ControlledFixedReserve.covariance P Λ (U ω) (dir ω)
          (fixedProfile P Λ (U ω) (dir ω) lo hi) σ target center ((q:ℝ)-(v:ℝ)) θ) E| ≤ K*fresh := by
    have hprod0 : 0 ≤ ∏ j,scoreVariance
        (familyCovariance σ target center (referenceProfile P Λ (U ω) (dir ω)) lo hi j) (D j):=by
      apply Finset.prod_nonneg
      intro j _
      apply scoreVariance_nonneg _ (hD ω j)
      exact OldIntervalCovariance.covariance_posSemidef σ target center hages _
        (referenceProfile_measurable P Λ (U ω) (dir ω))
        (fun p=>⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans
          (referenceProfile_bounds P Λ (U ω) (dir ω) p).1,
          (referenceProfile_bounds P Λ (U ω) (dir ω) p).2⟩) (lo j) (hi j)
    simp only [scale,Bool.false_eq_true,ite_false]
    rw [abs_of_nonneg (mul_nonneg hprod0 (sqrt_nonneg _))]
    exact mul_le_mul (holdScore ω) (hy ω θ).2 (sqrt_nonneg _) hK
  have hh:=MixedPastWordMoments.moment_on_past_event
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ v q hvq hqH hspan
    σ target center hσ hσ1 hages hgap lo hi hlo hlohi hstop hdisjoint false D E hD hE g leaf hnative ht
    F hFm hA0 hν hf hfb b hb0 B0 hBDG (K*fresh) (mul_nonneg hK hfresh0) hscore A hA
  convert! hh using 1

end SHE.MixedPastDecayedWord
