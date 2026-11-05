module

public import SHE.MixedPastOmittedWeights
public import SHE.OmittedVaryingMoments
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

namespace SHE.MixedPastOmittedMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOmittedMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOmittedMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOmittedMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOmittedMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOmittedMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOmittedMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedPastOmittedMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOmittedMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

include hIJ₀ hIJ₁ in
/-- Omitted-baseline assigned Gaussian moments at the ACTUAL random
past reference and native joint current. An arbitrary past-measurable
energy may remain correlated with every current/score/leaf. The erased
leaf contributes no fictitious rough moment, and every surviving block
retains its original gap and full-age gain. -/
theorem assigned_moment_with_past_weight (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (D : Fin r→State n)
    (hD : ∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup) (j0 : Fin m)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (K : ℝ) (hK : 0≤K)
    (hgeom : ∀ ω,|(∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j) (D j))*
      VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
      ∏ j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi
        (target (leaf j)) (chosen j)|≤K)
    (weight : Ω→ℝ) (hw : Measurable[𝓕 v] weight) (hw0 : ∀ ω,0≤weight ω)
    (hwi : Integrable weight μ) :
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean:=MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
    let G:=fun ω=>OmittedAssignedMoments.fibreAverage P Λ (U ω) (dir ω) θ ((q:ℝ)-(v:ℝ))
      σ target center lo hi (mean ω) D g leaf choices j0 F
    Integrable (fun ω=>weight ω*|G ω|^(2*b)) μ ∧ (∫ ω,weight ω*|G ω|^(2*b) ∂μ)≤
      OmittedAssignedMoments.constant P r m choices j0 b
        ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
          K^(2*b)*(∫ ω,weight ω ∂μ) := by
  intro U dir mean G
  let budget:=fun ω=>currentBudget P Λ (U ω) (dir ω) θ target center leaf (mean ω) b
  have hU : Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir : Measurable dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm:=MixedPastJointData.mean_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hG : Measurable G:=OmittedAssignedMoments.fibreAverage_measurable P Λ θ ((q:ℝ)-(v:ℝ))
    U dir hU hdir σ target center lo hi mean hm (fun _=>D) (fun _=>measurable_const)
    g leaf choices j0 F hFm
  have hc:=MixedPastOmittedWeights.constant_with_past_weight
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspan σ target center leaf hnative (fun j=>(ht j).1) (fun j=>hgap (leaf j))
    choices j0 b hb B0 hBDG weight hw hw0 hwi
  have hp (ω:Ω) : weight ω*|G ω|^(2*b)≤
      K^(2*b)*(weight ω*OmittedAssignedMoments.constant P r m choices j0 b (budget ω)) := by
    have hh:=OmittedAssignedMoments.pointwise_even_moment P Λ (U ω) (dir ω) θ
      ((q:ℝ)-(v:ℝ)) (sub_nonneg.mpr (by exact_mod_cast hvq)) σ target center hσ hσ1 hages
      lo hi hlo hlohi hstop hdisjoint (mean ω) D (hD ω) g leaf hnative ht choices hnd j0
      chosen hchosen F hFm hA0 hν hf hfb b hb
    have hC : 0≤OmittedAssignedMoments.constant P r m choices j0 b (budget ω):=
      OmittedAssignedMoments.constant_nonneg P b choices j0
        (NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1))
    have hscale:=pow_le_pow_left₀ (abs_nonneg _) (hgeom ω) (2*b)
    rw [pow_abs_two_mul] at hscale
    have hh2:=hh.trans (mul_le_mul_of_nonneg_left hscale hC)
    have hh3:=mul_le_mul_of_nonneg_left hh2 (hw0 ω)
    convert! hh3 using 1 <;> ring
  have hdom:=hc.1.const_mul (K^(2*b))
  have hmeas:=(hw.mono (𝓕.le v) le_rfl).mul ((continuous_abs.measurable.comp hG).pow_const (2*b))
  have hi : Integrable (fun ω=>weight ω*|G ω|^(2*b)) μ:=hdom.mono' hmeas.aestronglyMeasurable
    (ae_of_all _ (fun ω=>by rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (hw0 ω) (pow_nonneg (abs_nonneg _) _))];exact hp ω))
  refine ⟨hi,?_⟩
  have hbnd : (∫ ω,K^(2*b)*(weight ω*OmittedAssignedMoments.constant P r m choices j0 b (budget ω)) ∂μ)≤
      K^(2*b)*(OmittedAssignedMoments.constant P r m choices j0 b
        ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*(∫ ω,weight ω ∂μ)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hc.2 (pow_nonneg hK _)
  have hh:=(integral_mono hi hdom hp).trans hbnd
  convert! hh using 1 <;> ring

end SHE.MixedPastOmittedMoments

