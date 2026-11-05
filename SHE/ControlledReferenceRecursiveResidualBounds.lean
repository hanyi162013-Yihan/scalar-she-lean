module

public import SHE.ControlledReferenceResidual
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.PastParameterSectionExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.ControlledReferenceRecursiveResidualBounds
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

/-- At each fixed finite depth and time cutoff, the actual recursive
leaf, Gaussian reference, scalar insertion, retained common-Haar mark,
and full first-defect residual all admit one genuine bound uniform over
both past states, heat regularization and all history/sample values. -/
theorem uniform_piece_bounds (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ (p : ControlledProfile.Inputs) (ε : ℝ≥0) (h : CutoffWordHistories.History Unit k) (ω : Ω),
    ‖MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤K ∧
    ‖MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤K ∧
    ‖MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤K ∧
    ‖MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤K ∧
    ‖MixedJointPastExpectedLevel.noiseVersion 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤K := by
  let J := ControlledReferenceRecursiveBounds.test P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ k
  have hJ := ControlledReferenceRecursiveBounds.test_uniform P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ k
  obtain ⟨C,hCn,hC⟩ := hJ.norm_bound
  obtain ⟨D,hDn,hD⟩ := hJ.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := hJ.fderiv.fderiv.norm_bound
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hA : 0≤κ+M := add_nonneg hκ.le hM
  have haB (z : ℝ) : |κ+aV z|≤κ+M := by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbV z).1))]
    exact add_le_add le_rfl (hbV z).2
  let K₁ := ((1/2:ℝ)*(κ+M+P.upper)*B*((n+k:ℕ):ℝ))*PhysicalRemainderMass.heatMass (b:ℝ)
  let K₂ := (((n+k:ℕ):ℝ)^2*M*B)*PhysicalRemainderMass.heatMass (b:ℝ)
  have hK₁ : 0≤K₁ := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA P.upper_nonneg)) hBn) (by positivity))
    (PhysicalRemainderMass.heatMass_nonneg b.2)
  have hK₂ : 0≤K₂ := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hM) hBn)
    (PhysicalRemainderMass.heatMass_nonneg b.2)
  have hH (p : Inputs) (ε : ℝ≥0) (q : (CutoffWordHistories.History Unit k×Ω)×ℝ) :
      ‖JointWordHessian.field (L p ε k) Λ U V XU XV q‖≤B :=
    BackwardRegularity.gaussian_state_hessian_bound _ (((L p ε k).test_uniform.smooth q.1.1).of_le (by simp))
      (hC (p,(ε,q.1.1))) (hD (p,(ε,q.1.1))) (hB (p,(ε,q.1.1))) _
  have hmark (p : Inputs) (ε : ℝ≥0) (h : CutoffWordHistories.History Unit k) (ω : Ω) :
      ‖MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤K₂ := by
    let E := MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k)
    let I := JointWordDefect.integrand (L p ε k) Λ U V XU XV E
    let T := (L p ε k).terminal h
    have hvT : (v:ℝ)≤T := (L p ε k).terminal_base h
    have hb (t : ℝ) (ht : t∈Ioo (v:ℝ) T) :
        ‖I ((h,ω),t)‖≤(((n+k:ℕ):ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*(T-t)^(-(1/2:ℝ))) :=
      JointWordDefect.integrand_bound (L p ε k) Λ hM hBn (hH p ε)
        (fun q ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (L p ε k) hΛ q ω ht) h ω ht
    have hi := CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := T) (((n+k:ℕ):ℝ)^2*M*B)
    have hd : ∀ᵐ t∂volume,t∈Ioc (v:ℝ) T → ‖I ((h,ω),t)‖≤
        (((n+k:ℕ):ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*(T-t)^(-(1/2:ℝ))) := by
      filter_upwards [volume.ae_ne T] with t hne ht
      exact hb t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    have hh := intervalIntegral.norm_integral_le_of_norm_le hvT hd hi
    rw [intervalIntegral.integral_const_mul,PhysicalRemainderMass.heat_majorant_mass hvT] at hh
    have hTb : T≤(b:ℝ) := (L p ε k).terminal_horizon h
    exact hh.trans (mul_le_mul_of_nonneg_left
      (PhysicalRemainderMass.heatMass_mono (sub_nonneg.mpr hvT)
        (by linarith [v.2] : T-(v:ℝ)≤b)) (by positivity))
  refine ⟨2*C+K₁+K₂,by positivity,fun p ε h ω => ?_⟩
  have hl : ‖MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤C := hC (p,(ε,h)) _
  have hr : ‖MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤C :=
    GaussianSmooth.average_norm_bound _ (hC (p,(ε,h))) _
  have hc : ‖MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω‖≤K₁ :=
    JointInsertionBounds.remainder_bound (L p ε k) Λ U V XU XV hA haB hBn
      (fun h => hC (p,(ε,h))) (fun h => hD (p,(ε,h))) (fun h => hB (p,(ε,h))) h ω
  have hm := hmark p ε h ω
  refine ⟨by linarith,by linarith,by linarith,by linarith,?_⟩
  unfold MixedJointPastExpectedLevel.noiseVersion
  have hh := (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hl hr)) hc)) hm)
  nlinarith only [hh]

end SHE.ControlledReferenceRecursiveResidualBounds
