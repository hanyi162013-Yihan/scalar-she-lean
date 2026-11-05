module

public import SHE.MixedPastTwoFreshOffsetWeights
public import SHE.TwoFreshCompleteWord
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

namespace SHE.MixedPastTwoFreshCompleteWeights
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastTwoFreshCompleteWeights_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastTwoFreshCompleteWeights_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastTwoFreshCompleteWeights_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastTwoFreshCompleteWeights_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastTwoFreshCompleteWeights_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastTwoFreshCompleteWeights_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedPastTwoFreshCompleteWeights_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastTwoFreshCompleteWeights_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  TwoFreshFullResidualMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

include hIJ₀ hIJ₁ in
/-- Conditional native offsets control the complete finite-assignment
Gaussian constant against any actual past-measurable input energy. All
the constants are integrated before any deterministic geometric cap is
used, so dependence between the native current and the reference is kept. -/
theorem constant_with_past_weight (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (leaf : Fin m→Fin n) (hnative : ∀ j,σ (leaf j)=target (leaf j))
    (hage : ∀ j,0<target (leaf j)) (hgap : ∀ j,(q:ℝ)-(v:ℝ)<target (leaf j))
    (b : ℕ) (hb : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (weight : Ω→ℝ) (hw : Measurable[𝓕 v] weight) (hw0 : ∀ ω,0≤weight ω)
    (hwi : Integrable weight μ) :
    let U := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean := MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
    let budget := fun ω=>currentBudget P Λ (U ω) (dir ω) θ target center leaf (mean ω) b
    Integrable (fun ω=>weight ω*TwoFreshCompleteWord.momentConstant P r m b (budget ω)) μ ∧
      (∫ ω,weight ω*TwoFreshCompleteWord.momentConstant P r m b (budget ω) ∂μ)≤
        TwoFreshCompleteWord.momentConstant P r m b
          ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
            (∫ ω,weight ω ∂μ) := by
  intro U dir mean budget
  let cs:=assignments (m:=m+1) (List.finRange r)
  let R:=((1/2:ℝ)^r)^(2*b)*(cs.length:ℝ)^(2*b-1)
  let Cbar:=(m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent
  have hR : 0≤R:=by positivity
  have hM : 0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hCbar : 0≤Cbar:=by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.rpow_nonneg
    unfold NativeHybridMoments.momentConstant
    exact mul_nonneg B0.2 (pow_nonneg
      (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)
  have hbudget (ω:Ω) : 0≤budget ω:=
    NormalizedLeafOffsets.budget_nonneg _ _ _ _ hage
  have he (a:ℝ) (ha:0≤a) : TwoFreshCompleteWord.momentConstant P r m b a=
      R*(cs.map (fun choices=>constant P r m choices b a)).sum := by
    unfold TwoFreshCompleteWord.momentConstant
    change R*(cs.map (fun choices=>max (constant P r m choices b a) 0)).sum=_
    congr 1
    apply congrArg List.sum
    exact List.map_congr_left (fun choices _=>max_eq_left (constant_nonneg P b choices ha))
  have hc (choices : List (Fin r×Fin (m+1))) := MixedPastTwoFreshOffsetWeights.constant_with_past_weight
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspan σ target center leaf hnative hage hgap choices b hb B0 hBDG weight hw hw0 hwi
  have hi : Integrable (fun ω=>R*(cs.map (fun choices=>weight ω*constant P r m choices b (budget ω))).sum) μ :=
    (GaussianFreshSum.integrable_sum μ cs _ (fun choices _=>(hc choices).1)).const_mul R
  have hval (ω:Ω) : weight ω*TwoFreshCompleteWord.momentConstant P r m b (budget ω)=
      R*(cs.map (fun choices=>weight ω*constant P r m choices b (budget ω))).sum := by
    rw [he _ (hbudget ω),List.sum_map_mul_left]
    ring
  refine ⟨hi.congr (ae_of_all _ (fun ω=>(hval ω).symm)),?_⟩
  simp_rw [hval]
  rw [integral_const_mul,GaussianFreshSum.integral_sum μ cs _ (fun choices _=>(hc choices).1)]
  have hs : (cs.map (fun choices=>∫ ω,weight ω*constant P r m choices b (budget ω) ∂μ)).sum≤
      (cs.map (fun choices=>constant P r m choices b Cbar*(∫ ω,weight ω ∂μ))).sum :=
    List.sum_le_sum (fun choices _=>(hc choices).2)
  have hh:=mul_le_mul_of_nonneg_left hs hR
  rw [List.sum_map_mul_right,←mul_assoc,←he Cbar hCbar] at hh
  simpa only [mul_assoc] using hh

end SHE.MixedPastTwoFreshCompleteWeights

