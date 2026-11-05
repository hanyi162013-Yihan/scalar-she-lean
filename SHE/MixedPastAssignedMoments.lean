module

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

namespace SHE.MixedPastAssignedMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastAssignedMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastAssignedMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastAssignedMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastAssignedMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastAssignedMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastAssignedMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedPastAssignedMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastAssignedMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

/-- Exact varying-reference assigned Gaussian average based on the
ACTUAL random U_v,V_v-U_v and actual theta-interpolated stopped current. -/
def average (P : CanonicalCovariance.ProfileParameters) (v q : ℝ≥0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (second : Bool) (D : Fin r→State n) (E : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ) (ω : Ω) : ℝ :=
  fibreAverage P Λ
    (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
    (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
    θ ((q:ℝ)-(v:ℝ)) σ target center lo hi
    (MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center ω)
    second D E g leaf choices F

include hIJ₀ hIJ₁ in
/-- The all-order assigned Gaussian estimate on EVERY actual past event.
All random-profile/current-state applicability and Borel fields are
proved. The remaining geometric score cap K is deterministic and can
be the true old-parent/fresh-row envelope. -/
theorem moment_on_past_event (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (second : Bool) (D : Fin r→State n) (E : State n)
    (hD : ∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j)).range)
    (hE : ∀ ω,E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (fixedProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) lo hi)
        σ target center ((q:ℝ)-(v:ℝ)) θ)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (K : ℝ) (hK : 0≤K)
    (hgeom : ∀ ω,
      let u := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω
      let dir := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω
      let A := familyCovariance σ target center (referenceProfile P Λ u dir) lo hi
      let B := ControlledFixedReserve.covariance P Λ u dir (fixedProfile P Λ u dir lo hi) σ target center ((q:ℝ)-(v:ℝ)) θ
      |((∏ j,scoreVariance (A j) (D j))*scale second B E)*
        VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
        ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)|≤K)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    let G := average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ P v q σ target center lo hi
      second D E g leaf choices F
    Integrable (fun ω=>|G ω|^(2*b)) (μ.restrict A) ∧
      (∫ ω in A,|G ω|^(2*b) ∂μ)≤
        constant P r m choices b ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
          K^(2*b)*μ.real A := by
  intro G
  let U := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  let dir := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  let mean := MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hU : Measurable U := (MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir : Measurable dir := (MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm := MixedPastJointData.mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hG := VaryingControlledGaussianFields.fibreAverage_measurable P Λ θ ((q:ℝ)-(v:ℝ)) U dir hU hdir
    σ target center lo hi mean hm second (fun _=>D) (fun _=>measurable_const) (fun _=>E) measurable_const
    g leaf choices F hFm
  have hoffset (j : Fin m) := MixedPastJointData.native_leaf_moment_on_past_event
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ hlocal hΛ hθ v q hvq hqH hspan
    σ target center (leaf j) (hnative j) (ht j).1 (hgap _) (b*(m+2)) (Nat.mul_pos hb0 (by omega)) B0 hBDG
    P.exponent_pos.le P.exponent_le_one A hA
  have hh := varying_even_moment (μ.restrict A) P Λ U dir θ ((q:ℝ)-(v:ℝ))
    (sub_nonneg.mpr (by exact_mod_cast hvq)) σ target center hσ hσ1 hages lo hi hlo hlohi hstop hdisjoint
    mean second (fun _=>D) hD (fun _=>E) hE g leaf hnative ht choices hnd chosen hchosen F hFm hA0 hν hf hfb b hb0
    ((NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)
    (fun j=>by simpa only [U,dir,mean,measureReal_restrict_apply_univ] using hoffset j) hG K hK (ae_of_all _ hgeom)
  simpa only [G,average,U,dir,mean,measureReal_restrict_apply_univ] using hh

end SHE.MixedPastAssignedMoments
