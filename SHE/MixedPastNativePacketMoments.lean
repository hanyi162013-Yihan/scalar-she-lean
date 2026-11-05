module

public import SHE.MixedPastNativePacketEnergy
public import SHE.MixedPastNativeFirstWholeCompleteWeights
public import SHE.MixedPastTwoFreshCompleteWeights
public import SHE.ControlledFutureFields
public import SHE.SectionEnergy
public import SHE.NativeFirstWholeComplete
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

namespace SHE.MixedPastNativePacketMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativePacketMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativePacketMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativePacketMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativePacketMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativePacketMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativePacketMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastNativePacketMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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


local instance mixedPastNativePacketMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativePacketMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  NativeFirstWholeMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

include hIJ₀ hIJ₁ in
/-- The literal actual Gaussian-offset budget has a uniform joint
sample/output first moment, derived from native moments on past events. -/
theorem budget_energy (P:CanonicalCovariance.ProfileParameters)
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (θ:ℝ) (hθ:|θ|≤1)
    (v q:ℝ≥0) (hvq:v≤q) (hqH:q≤H) (hspan:(q:ℝ)-(v:ℝ)≤1)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n)
    (hnative:∀j,σ (leaf j)=target (leaf j)) (hage:∀j,0<target (leaf j))
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i) (p:ℕ) (hp:0<p)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (p*(m+2)) J B0):
    let C:=(m:ℝ)*(NativeHybridMoments.momentConstant (p*(m+2)) B0 κ M)^P.exponent
    let f:=fun z:Ω×UnitAddCircle=>MixedPastNativePacketEnergy.budget
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf p (θ,z)
    Integrable f (μ.prod AddCircle.haarAddCircle) ∧
      (∫z,f z ∂μ.prod AddCircle.haarAddCircle)≤C:=by
  intro C f
  have hfm:Measurable f:=(MixedPastNativePacketEnergy.budget_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf p hgap).comp
      (measurable_const.prodMk measurable_id)
  have hfn(z:Ω×UnitAddCircle):0≤f z:=NormalizedLeafOffsets.budget_nonneg _ _ _ _ hage
  have hs(x:UnitAddCircle):Integrable (fun ω=>f (ω,x)) μ ∧ (∫ω,f (ω,x) ∂μ)≤C:=by
    let center:=StoppedGaussianScore.nativeCenter (fun i=>a i+x)
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let D:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean:=MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
    let off:=fun ω j=>mean ω (leaf j)-ControlledProfile.mean Λ (U ω) (D ω) (θ,(target (leaf j),center (leaf j)))
    have he(j:Fin m):Integrable (fun ω=>|off ω j|^(((2*(p*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
        (∫ω,|off ω j|^(((2*(p*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
          (NativeHybridMoments.momentConstant (p*(m+2)) B0 κ M)^P.exponent*
            (target (leaf j))^((p*(m+2):ℕ)*P.exponent/2)*μ.real Set.univ:=by
      simpa only [Measure.restrict_univ] using MixedPastJointData.native_leaf_moment_on_past_event
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ hlocal hΛ hθ
        v q hvq hqH hspan σ target center (leaf j) (hnative j) (hage j) (hgap (leaf j))
        (p*(m+2)) (Nat.mul_pos hp (by omega)) B0 hBDG P.exponent_pos.le P.exponent_le_one Set.univ MeasurableSet.univ
    have hi:=NormalizedLeafOffsets.budget_integrable μ (fun j=>target (leaf j)) off
      (((2*(p*(m+2)):ℕ):ℝ)*P.exponent) ((p*(m+2):ℕ)*P.exponent/2) (fun j=>(he j).1)
    refine ⟨hi,?_⟩
    have hb:=NormalizedLeafOffsets.integral_budget_le μ (fun j=>target (leaf j)) hage off
      (((2*(p*(m+2)):ℕ):ℝ)*P.exponent) ((p*(m+2):ℕ)*P.exponent/2)
      ((NativeHybridMoments.momentConstant (p*(m+2)) B0 κ M)^P.exponent)
      (fun j=>(he j).1) (fun j=>(he j).2)
    convert! (by simpa only [probReal_univ,mul_one] using hb) using 1
  have hmi:Integrable (fun x:UnitAddCircle=>∫ω,f (ω,x) ∂μ) AddCircle.haarAddCircle:=
    (integrable_const C).mono' (hfm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (ae_of_all _ (fun x=>by rw [Real.norm_of_nonneg (integral_nonneg (fun ω=>hfn (ω,x)))];exact (hs x).2))
  have hi:Integrable (fun z:UnitAddCircle×Ω=>f (z.2,z.1)) (AddCircle.haarAddCircle.prod μ):=by
    apply (integrable_prod_iff (hfm.comp measurable_swap).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x=>(hs x).1),?_⟩
    have he : (fun x:UnitAddCircle=>∫ω,‖(f ∘ Prod.swap) (x,ω)‖ ∂μ)=
        (fun x:UnitAddCircle=>∫ω,f (ω,x) ∂μ) := by
      funext x
      apply integral_congr_ae
      exact ae_of_all _ (fun ω=>Real.norm_of_nonneg (hfn (ω,x)))
    rw [he]
    exact hmi
  have hif : Integrable f (μ.prod AddCircle.haarAddCircle) := by convert! hi.swap using 1
  refine ⟨hif,?_⟩
  rw [integral_prod _ hif,integral_integral_swap hif]
  exact (integral_mono hmi (integrable_const C) (fun x=>(hs x).2)).trans_eq (by simp)

end SHE.MixedPastNativePacketMoments
