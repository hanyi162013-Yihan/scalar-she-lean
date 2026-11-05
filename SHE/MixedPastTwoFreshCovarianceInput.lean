module

public import SHE.MixedPastTwoFreshCompleteWeights
public import SHE.TwoFreshCovarianceInput
public import SHE.TwoFreshControlledFields
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

namespace SHE.MixedPastTwoFreshCovarianceInput
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastTwoFreshCovarianceInput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastTwoFreshCovarianceInput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastTwoFreshCovarianceInput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastTwoFreshCovarianceInput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastTwoFreshCovarianceInput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastTwoFreshCovarianceInput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
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

local instance mixedPastTwoFreshCovarianceInput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastTwoFreshCovarianceInput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  TwoFreshFullResidualMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

include hIJ₀ hIJ₁ in
/-- The COMPLETE covariance-input word at the ACTUAL random
past reference obeys its sharp input-mass bound. The signed continuum
input and its Gaussian score mass may vary with the observed past. The
native current remains correlated with both: density Jensen is applied
pathwise, then the true conditional offset budget is integrated against
the past-measurable mass. -/
theorem input_moment (νX : Measure X) [SFinite νX]
    (P : CanonicalCovariance.ProfileParameters)
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
    (E : State n) (hE : E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ)))).range)
    (row : X→State n) (hrow : Measurable row)
    (hB : ∀ ω,(ControlledFixedReserve.covariance P Λ
      (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
      (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) lo hi))
      σ target center ((q:ℝ)-(v:ℝ)) θ).PosSemidef)
    (hrowRange : ∀ ω,∀ᵐ x ∂νX,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) lo hi))
        σ target center ((q:ℝ)-(v:ℝ)) θ)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Set.Ioc 0 P.horizon)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ r F)
    (hfb : ∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (e : Ω×X→ℝ) (he : Measurable e)
    (hEnergy : ∀ ω,Integrable (fun x=>|e (ω,x)| *scoreVariance
      (ControlledFixedReserve.covariance P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ
          (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
          (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω) lo hi))
        σ target center ((q:ℝ)-(v:ℝ)) θ) (row x)) νX)
    (K : ℝ) (hK : 0≤K)
    (hgeom : ∀ ω,|∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j) (D j)|≤K) :
    let U := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean := MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
    let mass := fun ω=>∫ x,|e (ω,x)| *scoreVariance
      (ControlledFixedReserve.covariance P Λ (U ω) (dir ω) (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (U ω) (dir ω) lo hi))
        σ target center ((q:ℝ)-(v:ℝ)) θ) (row x) ∂νX
    Measurable[𝓕 v] (fun ω=>(mass ω)^(2*b))→Integrable (fun ω=>(mass ω)^(2*b)) μ→
    let G := fun ω=>(1/2:ℝ)*∫ x,e (ω,x)*TwoFreshCompleteWord.value P Λ (U ω) (dir ω) θ ((q:ℝ)-(v:ℝ))
      σ target center lo hi (mean ω) true D E (row x) g leaf F ∂νX
    Integrable (fun ω=>|G ω|^(2*b)) μ ∧ (∫ ω,|G ω|^(2*b) ∂μ)≤
      TwoFreshCompleteWord.momentConstant P r m b ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
        (K*Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*(∫ ω,(mass ω)^(2*b) ∂μ) := by
  intro U dir mean mass hmass hmassI G
  have hU : Measurable U := (MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir : Measurable dir := (MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm := MixedPastJointData.mean_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  let budget := fun ω=>currentBudget P Λ (U ω) (dir ω) θ target center leaf (mean ω) b
  have hc := MixedPastTwoFreshCompleteWeights.constant_with_past_weight (r:=r)
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspan σ target center leaf hnative (fun j=>(ht j).1) (fun j=>hgap (leaf j))
    b hb B0 hBDG (fun ω=>(mass ω)^(2*b)) hmass
      (fun ω=>(even_two_mul b).pow_nonneg (mass ω)) hmassI
  have hG : Measurable G := by
    let cs:=assignments (m:=m+1) (List.finRange r)
    have hinner : Measurable (fun z : Ω×X=>TwoFreshCompleteWord.value P Λ (U z.1) (dir z.1)
        θ ((q:ℝ)-(v:ℝ)) σ target center lo hi (mean z.1) true D E (row z.2) g leaf F) := by
      have heq : (fun z : Ω×X=>TwoFreshCompleteWord.value P Λ (U z.1) (dir z.1)
          θ ((q:ℝ)-(v:ℝ)) σ target center lo hi (mean z.1) true D E (row z.2) g leaf F)=
          (fun z=>(1/2:ℝ)^r*∑ j : Fin cs.length,fibreAverage P Λ (U z.1) (dir z.1) θ ((q:ℝ)-(v:ℝ))
            σ target center lo hi (mean z.1) true D E (row z.2) g leaf (cs.get j) F) :=
        funext (fun _=>congrArg (fun a:ℝ=>(1/2:ℝ)^r*a) (FiniteAssignmentMoments.map_sum_eq_fin cs _))
      rw [heq]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro j _
      exact TwoFreshControlledFields.fibreAverage_measurable P Λ θ ((q:ℝ)-(v:ℝ))
        (fun z : Ω×X=>U z.1) (fun z : Ω×X=>dir z.1) (hU.comp measurable_fst) (hdir.comp measurable_fst)
        σ target center lo hi (fun z : Ω×X=>mean z.1) (hm.comp measurable_fst) true
        (fun _=>D) (fun _=>measurable_const) (fun _=>E) (fun z : Ω×X=>row z.2)
        measurable_const (hrow.comp measurable_snd)
        g leaf (cs.get j) F hFm
    exact (((he.mul hinner).stronglyMeasurable.integral_prod_right').measurable).const_mul _
  have hp (ω : Ω) : |G ω|^(2*b)≤
      (K*Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*((mass ω)^(2*b)*TwoFreshCompleteWord.momentConstant P r m b (budget ω)) := by
    have hh := TwoFreshCovarianceInput.bound νX P Λ (U ω) (dir ω) θ
      ((q:ℝ)-(v:ℝ)) (sub_nonneg.mpr (by exact_mod_cast hvq)) σ target center hσ hσ1 hages
      lo hi hlo hlohi hstop hdisjoint (mean ω) D (hD ω) E hE row hrow (hB ω) (hrowRange ω)
      g leaf hnative ht F hFm hA0 hν hf hfb b hb
      (fun x=>e (ω,x)) (he.comp (measurable_const.prodMk measurable_id)) (hEnergy ω) K hK (hgeom ω)
    convert! hh using 1 <;> simp only [mul_pow] <;> ring
  have hci : Integrable (fun ω=>(K*Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*((mass ω)^(2*b)*TwoFreshCompleteWord.momentConstant P r m b (budget ω))) μ :=
    hc.1.const_mul _
  have hgi : Integrable (fun ω=>|G ω|^(2*b)) μ := hci.mono'
    ((continuous_abs.measurable.comp hG).pow_const _).aestronglyMeasurable
    (ae_of_all _ (fun ω=>by simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hp ω))
  refine ⟨hgi,?_⟩
  have hbnd : (∫ ω,(K*Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*((mass ω)^(2*b)*TwoFreshCompleteWord.momentConstant P r m b (budget ω)) ∂μ)≤
      (K*Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*(TwoFreshCompleteWord.momentConstant P r m b
        ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
          (∫ ω,(mass ω)^(2*b) ∂μ)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hc.2 ((even_two_mul b).pow_nonneg _)
  have hh := (integral_mono hgi hci hp).trans hbnd
  convert! hh using 1 <;> ring

end SHE.MixedPastTwoFreshCovarianceInput

