module

public import SHE.MixedPastTerminalCovarianceWeights
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

namespace SHE.MixedPastTerminalCompleteWeights
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

include hIJ₀ hIJ₁ in
/-- The complete assignment constant at the literal physical terminal
state, averaged against any observed-past energy on ONE spatial event. -/
theorem constant_with_past_weight (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v<q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (leaf : Fin m→Fin (n+1))
    (hnative : ∀ j,(Fin.cons ((q:ℝ)-(v:ℝ)) σ : Fin (n+1)→ℝ) (leaf j)=
      (Fin.cons ((q:ℝ)-(v:ℝ)) target : Fin (n+1)→ℝ) (leaf j))
    (b : ℕ) (hb : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ weight : Ω→ℝ,
      Measurable[𝓕 v] weight → (∀ ω,0≤weight ω) → Integrable weight μ →
    let U := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean := MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center x
    let budget := fun ω=>currentBudget P Λ (U ω) (dir ω) θ
      (Fin.cons ((q:ℝ)-(v:ℝ)) target) (Fin.cons x center) leaf (mean ω) b
    Integrable (fun ω=>weight ω*MixedPastWordMoments.momentConstant P r m b (budget ω)) μ ∧
      (∫ ω,weight ω*MixedPastWordMoments.momentConstant P r m b (budget ω) ∂μ)≤
        MixedPastWordMoments.momentConstant P r m b
          ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
            (∫ ω,weight ω ∂μ) := by
  have hp (choices : List (Fin r×Fin (m+1))) :=
    MixedPastTerminalCovarianceWeights.constant_with_past_weight
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
      v q hvq hqH hspan σ target center hgap leaf hnative choices b hb B0 hBDG
  have hall := (ae_all_iff).mpr hp
  filter_upwards [hall] with x hx
  intro weight hw hw0 hwi U dir mean budget
  have hage (j : Fin m) : 0<(Fin.cons ((q:ℝ)-(v:ℝ)) target : Fin (n+1)→ℝ) (leaf j) := by
    have hqv : 0<(q:ℝ)-(v:ℝ) := sub_pos.mpr (by exact_mod_cast hvq)
    exact Fin.cases hqv (fun i=>lt_trans hqv (hgap i)) (leaf j)
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
  have he (a:ℝ) (ha:0≤a) : MixedPastWordMoments.momentConstant P r m b a=
      R*(cs.map (fun choices=>constant P r m choices b a)).sum := by
    unfold MixedPastWordMoments.momentConstant
    change R*(cs.map (fun choices=>max (constant P r m choices b a) 0)).sum=_
    congr 1
    apply congrArg List.sum
    exact List.map_congr_left (fun choices _=>max_eq_left (constant_nonneg P b choices ha))
  have hc (choices : List (Fin r×Fin (m+1))) := hx choices weight hw hw0 hwi
  have hi : Integrable (fun ω=>R*(cs.map (fun choices=>weight ω*constant P r m choices b (budget ω))).sum) μ :=
    (GaussianFreshSum.integrable_sum μ cs _ (fun choices _=>(hc choices).1)).const_mul R
  have hval (ω:Ω) : weight ω*MixedPastWordMoments.momentConstant P r m b (budget ω)=
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

end SHE.MixedPastTerminalCompleteWeights
