module

public import SHE.PairedSlotAverages
public import SHE.MixedPastPairedRoughMoments
public import SHE.PairedRoughFields
public import SHE.NormalizedOffsetWeights
public import SHE.MixedPastTerminalData
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

namespace SHE.MixedPastLiteralRoughSlot
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastPairedRoughMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastPairedRoughMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastPairedRoughMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastPairedRoughMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastPairedRoughMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastPairedRoughMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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



local instance mixedPastPairedRoughMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastPairedRoughMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}
local instance mixedPastPairedRoughMoments_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩

include hIJ₀ hIJ₁ in
theorem conditional_rough_slot (P:CanonicalCovariance.ProfileParameters)
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (v q:ℝ≥0) (hvq:v<q) (hqH:q≤H) (hspan:(q:ℝ)-(v:ℝ)≤1)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i) (hσ1:∀i,σ i≤1) (hages:∀i,σ i≤target i)
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i)
    (lo hi:Fin r→ℝ) (hlo:∀j,(q:ℝ)-(v:ℝ)≤lo j) (hlohi:∀j,lo j<hi j)
    (hstop:∀j i,σ i≤lo j ∨ hi j≤σ i) (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (D:HeatCircle→Fin r→State (n+1)) (g:Fin 1→Fin (n+1)) (leaf:Fin m→Fin (n+1))
    (hnative:∀j,(Fin.cons ((q:ℝ)-(v:ℝ)) σ:Fin (n+1)→ℝ) (leaf j)=
      (Fin.cons ((q:ℝ)-(v:ℝ)) target:Fin (n+1)→ℝ) (leaf j))
    (ht:∀j,(Fin.cons ((q:ℝ)-(v:ℝ)) target:Fin (n+1)→ℝ) (leaf j)∈Set.Ioc 0 P.horizon)
    (choices:List (Fin r×Fin (m+1))) (hnd:(choices.map Prod.fst).Nodup)
    (chosen:∀j:Fin m,GaussianAssignmentBlocks.block choices j.succ≠[]→Fin r)
    (hchosen:∀j h,chosen j h∈GaussianAssignmentBlocks.block choices j.succ)
    (j0:Fin m) (F:State 1→ℝ) (hF:Measurable F) {A0 ν χ:ℝ}
    (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hf:ContDiff ℝ (GaussianAssignmentBlocks.block choices 0).length F)
    (hfb:∀j,j≤(GaussianAssignmentBlocks.block choices 0).length→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b:ℕ) (hb:0<b) (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (b*(m+2)) J B0) :
    ∀ᵐ x:HeatCircle ∂haarAddCircle,
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let sσ:Fin (n+1)→ℝ:=Fin.cons ((q:ℝ)-(v:ℝ)) σ
    let sT:Fin (n+1)→ℝ:=Fin.cons ((q:ℝ)-(v:ℝ)) target
    let sx:Fin (n+1)→HeatCircle:=Fin.cons x center
    let mean:=fun θ=>MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center x
    (∀ω j,D x j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance sσ sT sx (referenceProfile P Λ (U ω) (dir ω)) lo hi j)).range) →
    ∀K:ℝ,0≤K →
    (∀ᵐ ω ∂μ,|(∏j,scoreVariance (familyCovariance sσ sT sx (referenceProfile P Λ (U ω) (dir ω)) lo hi j) (D x j))*
      VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1*
      ∏j,PairedRoughVaryingMoments.leafScale P choices j0 χ lo hi sT leaf chosen j|≤K) →
    ∀A:Set Ω,MeasurableSet[𝓕 v] A →
    let G:=fun ω=>PairedAssignedTelescope.averageSlot P Λ (U ω) (dir ω) 0 1 0 ((q:ℝ)-(v:ℝ))
      sσ sT sx lo hi (D x) choices F g leaf (mean 1 ω) (mean 0 ω) ν χ j0.succ
    Integrable (fun ω=>|G ω|^(2*b)) (μ.restrict A) ∧
      (∫ω in A,|G ω|^(2*b) ∂μ)≤PairedRoughWordMoments.constant P choices j0 χ b
        (2*(m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*K^(2*b)*μ.real A := by
  have hh:=MixedPastPairedRoughMoments.conditional_even_moment
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P hlocal hΛ v q hvq hqH hspan σ target center hσ hσ1 hages hgap
    lo hi hlo hlohi hstop hdisjoint D g leaf hnative ht choices hnd chosen hchosen
    (fun j=>decide (j0<j)) j0 F hF hA0 hν hχ hχβ hf hfb b hb B0 hBDG
  simpa only [PairedAssignedTelescope.averageSlot_rough] using hh

end SHE.MixedPastLiteralRoughSlot
