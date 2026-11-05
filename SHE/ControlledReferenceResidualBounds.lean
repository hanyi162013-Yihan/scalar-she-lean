module

public import SHE.ControlledReferenceResidual
public import SHE.PastParameterSectionExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.ControlledReferenceResidualBounds
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
local notation "L" p => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF p

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

/-- Uniformity over BOTH original state parameters is derived from
actual bounded test derivatives and the physical endpoint heat majorant.
It is not a supplied random-reference domination assumption. -/
theorem uniform_piece_bounds (hΛ : 0≤Λ) : ∃ K : ℝ,0≤K ∧ ∀ p ω,
    ‖MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤K ∧
    ‖MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤K ∧
    ‖MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤K ∧
    ‖MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤K ∧
    ‖ControlledReferenceResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF p ω‖≤K := by
  obtain ⟨C,hCn,hC⟩ := (UniformSmooth.UniformBoundedSmooth.fixed (P := Unit) hF).norm_bound
  obtain ⟨D,hDn,hD⟩ := (UniformSmooth.UniformBoundedSmooth.fixed (P := Unit) hF).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (UniformSmooth.UniformBoundedSmooth.fixed (P := Unit) hF).fderiv.fderiv.norm_bound
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hA : 0≤κ+M := add_nonneg hκ.le hM
  have haB (z : ℝ) : |κ+aV z|≤κ+M := by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbV z).1))]
    exact add_le_add le_rfl (hbV z).2
  let K₁ := ((1/2:ℝ)*(κ+M+P.upper)*B*n)*PhysicalRemainderMass.heatMass (b:ℝ)
  let K₂ := ((n:ℝ)^2*M*B)*PhysicalRemainderMass.heatMass (b:ℝ)
  have hK₁ : 0≤K₁ := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA P.upper_nonneg)) hBn) (Nat.cast_nonneg _))
    (PhysicalRemainderMass.heatMass_nonneg b.2)
  have hK₂ : 0≤K₂ := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hM) hBn)
    (PhysicalRemainderMass.heatMass_nonneg b.2)
  have hH (p : Inputs) (q : (Unit×Ω)×ℝ) :
      ‖JointWordHessian.field (L p) Λ U V XU XV q‖≤B := by
    exact BackwardRegularity.gaussian_state_hessian_bound _ (hF.smooth.of_le (by simp))
      (hC ()) (hD ()) (hB ()) _
  have hmark (p : Inputs) (ω : Ω) :
      ‖MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤K₂ := by
    let E := MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p)
    let I := JointWordDefect.integrand (L p) Λ U V XU XV E
    have hb (t : ℝ) (ht : t∈Ioo (v:ℝ) (b:ℝ)) :
        ‖I (((),ω),t)‖≤((n:ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*((b:ℝ)-t)^(-(1/2:ℝ))) :=
      JointWordDefect.integrand_bound (L p) Λ hM hBn (hH p)
        (fun q ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (L p) hΛ q ω ht) () ω ht
    have hvb' : (v:ℝ)≤(b:ℝ) := by exact_mod_cast hvb
    have hi := CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := (b:ℝ)) ((n:ℝ)^2*M*B)
    have hd : ∀ᵐ t∂volume,t∈Ioc (v:ℝ) (b:ℝ) → ‖I (((),ω),t)‖≤
        ((n:ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*((b:ℝ)-t)^(-(1/2:ℝ))) := by
      filter_upwards [volume.ae_ne (b:ℝ)] with t hne ht
      exact hb t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    have hh := intervalIntegral.norm_integral_le_of_norm_le hvb' hd hi
    rw [intervalIntegral.integral_const_mul,PhysicalRemainderMass.heat_majorant_mass hvb'] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (PhysicalRemainderMass.heatMass_mono (sub_nonneg.mpr hvb') (by linarith [v.2] : (b:ℝ)-(v:ℝ)≤b))
      (by positivity))
  refine ⟨2*C+K₁+K₂,by positivity,fun p ω => ?_⟩
  have hl : ‖MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤C := hC () _
  have hr : ‖MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤C :=
    GaussianSmooth.average_norm_bound _ (hC ()) _
  have hc : ‖MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p) () ω‖≤K₁ :=
    JointInsertionBounds.remainder_bound (L p) Λ U V XU XV hA haB hBn (fun _ => hC ())
      (fun _ => hD ()) (fun _ => hB ()) () ω
  have hm := hmark p ω
  refine ⟨by linarith,by linarith,by linarith,by linarith,?_⟩
  unfold ControlledReferenceResidual.residual MixedJointPastExpectedLevel.noiseVersion
  have hh := (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hl hr)) hc)) hm)
  nlinarith only [hh]

theorem uniform_bound (hΛ : 0≤Λ) : ∃ K : ℝ,0≤K ∧ ∀ p ω,
    ‖ControlledReferenceResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF p ω‖≤K := by
  obtain ⟨K,hK,hb⟩ := uniform_piece_bounds 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hΛ
  exact ⟨K,hK,fun p ω => (hb p ω).2.2.2.2⟩

end SHE.ControlledReferenceResidualBounds

