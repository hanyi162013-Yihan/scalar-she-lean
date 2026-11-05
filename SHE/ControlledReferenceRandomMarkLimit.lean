module

public import SHE.MixedNativeRandomRecursiveIdentity
public import SHE.MixedJointUncutMark
public import SHE.ControlledReferenceUncutBounds
public import SHE.DominatedCutoffLimit
public import SHE.FiniteParameterL1Limit
public import SHE.JointRecursiveReferenceLimit
public import SHE.JointRecursiveRemainderConvergence
public import SHE.MixedJointMarkConvergence
public import SHE.ControlledReferenceRecursiveResidualBounds
public import SHE.ControlledReferenceRecursiveResidualContinuity
public import SHE.PastParameterHistoryExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.ControlledReferenceRandomMarkLimit
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
local instance controlledReferenceRandomMarkLimit_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
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


local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open Filter Topology
local notation "Base" => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF

open CutoffWordHistories UncutWordEvaluation
local notation "NL" => (fun p k => normalizedLevel (Base p) k)
local notation "Mmark" => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "UM" => (fun p k h ω => MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k h ω)
local notation "CM" => (fun p δ k h ω => MixedJointUncutMark.cutoffMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) δ k h ω)
local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)

theorem normalized_mark_bound (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ (p : Inputs) (h : History Unit k) ω,
    ‖Mmark (NL p k) h ω‖≤K := by
  have hJ := ControlledReferenceUncutBounds.normalized_uniform P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF k
  obtain ⟨C,hCn,hC⟩ := hJ.norm_bound
  obtain ⟨D,hDn,hD⟩ := hJ.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := hJ.fderiv.fderiv.norm_bound
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  let K := (((n+k:ℕ):ℝ)^2*M*B)*PhysicalRemainderMass.heatMass (b:ℝ)
  have hKn : 0≤K := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hM) hBn)
    (PhysicalRemainderMass.heatMass_nonneg b.2)
  refine ⟨K,hKn,fun p h ω => ?_⟩
  let E := MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL p k)
  let I := JointWordDefect.integrand (NL p k) Λ U V XU XV E
  let T := (NL p k).terminal h
  have hvT : (v:ℝ)≤T := (NL p k).terminal_base h
  have hH (q : (History Unit k×Ω)×ℝ) : ‖JointWordHessian.field (NL p k) Λ U V XU XV q‖≤B :=
    BackwardRegularity.gaussian_state_hessian_bound _ (((NL p k).test_uniform.smooth q.1.1).of_le (by simp))
      (hC (p,q.1.1)) (hD (p,q.1.1)) (hB (p,q.1.1)) _
  have hb (t : ℝ) (ht : t∈Ioo (v:ℝ) T) :
      ‖I ((h,ω),t)‖≤(((n+k:ℕ):ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*(T-t)^(-(1/2:ℝ))) :=
    JointWordDefect.integrand_bound (NL p k) Λ hM hBn hH
      (fun q ω t ht => MixedJointLevelData.defect_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (NL p k) hΛ q ω ht) h ω ht
  have hi := CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := T) (((n+k:ℕ):ℝ)^2*M*B)
  have hd : ∀ᵐ t∂volume,t∈Ioc (v:ℝ) T → ‖I ((h,ω),t)‖≤
      (((n+k:ℕ):ℝ)^2*M*B)*(1+StoppedFourier.heatConstant*(T-t)^(-(1/2:ℝ))) := by
    filter_upwards [volume.ae_ne T] with t hne ht
    exact hb t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le hvT hd hi
  rw [intervalIntegral.integral_const_mul,PhysicalRemainderMass.heat_majorant_mass hvT] at hh
  have hTb : T≤(b:ℝ) := (NL p k).terminal_horizon h
  exact hh.trans (mul_le_mul_of_nonneg_left
    (PhysicalRemainderMass.heatMass_mono (sub_nonneg.mpr hvT)
      (by linarith [v.2] : T-(v:ℝ)≤b)) (by positivity))

theorem mark_bound (hΛ : 0≤Λ) (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ (p : Inputs) (h : History Unit k) ω,
    ‖UM p k h ω‖≤K*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨K,hKn,hK⟩ := normalized_mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hΛ k
  refine ⟨K,hKn,fun p h ω => ?_⟩
  change ‖UncutSmoothWords.weight (Base p) k h*Mmark (NL p k) h ω‖≤_
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)]
  have hh := mul_le_mul_of_nonneg_left (hK p h ω) (UncutSmoothWords.weight_nonneg (Base p) k h)
  rw [ControlledReferenceUncutBounds.weight_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF p (0,0) k h] at hh
  rw [ControlledReferenceUncutBounds.weight_eq P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF p (0,0) k h]
  exact hh.trans_eq (mul_comm _ _)

variable (u : Ω→Inputs) (hu : StronglyMeasurable u)
include hsmall hu in
theorem cutoff_measurable (hΛ : 0≤Λ) (δ : ℝ) (hδ : 0<δ) (k : ℕ) :
    Measurable (fun q : History Unit k×Ω => CM (u q.2) δ k q.1 q.2) := by
  let Q := History Unit k×Ω
  let L := ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ
  have huQ : StronglyMeasurable (fun q : Q => u q.2) := hu.comp_measurable measurable_snd
  have hK (p : Inputs) : Measurable (fun q : Q => Mmark (L p 0 k) q.1 q.2) :=
    MixedJointLevelData.mark_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p 0 k)
  have hh := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl
    (fun p q => Mmark (L p 0 k) q.1 q.2) hK huQ
    (fun q => ControlledReferenceRecursiveResidualContinuity.continuous_mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ 0 k q.1 q.2)
  simpa only [MixedJointUncutMark.cutoffMark,dif_pos hδ,L,ControlledReferenceRecursiveBounds.level] using hh.measurable

include hsmall hu in
/-- The literal retained common-Haar mark admits the random-reference
cutoff limit under the common actual history measure. The uncut
majorant is independent of δ and both random past-state inputs. -/
theorem mark_converges (hΛ : 0≤Λ) (ν : Measure Unit) [IsFiniteMeasure ν]
    (τ : Measure Ω) [IsFiniteMeasure τ] (k : ℕ) :
    Tendsto (fun δ : ℝ => ∫ q : History Unit k×Ω,CM (u q.2) δ k q.1 q.2
      ∂(historyMeasure R₀ ν k).prod τ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ q : History Unit k×Ω,UM (u q.2) k q.1 q.2 ∂(historyMeasure R₀ ν k).prod τ)) := by
  obtain ⟨K,hKn,hK⟩ := mark_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hΛ k
  apply DominatedCutoffLimit.integral_tendsto ((historyMeasure R₀ ν k).prod τ)
    (W := fun q => UncutSmoothWords.weight (Base (0,0)) k q.1) (M := K)
    ((UncutHistoryMass.weight_integrable (Base (0,0)) ν k).comp_fst τ)
  · exact fun δ hδ => cutoff_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hsmall u hu hΛ δ hδ k
  · intro δ hδ q
    change ‖MixedJointUncutMark.cutoffMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base (u q.2)) δ k q.1 q.2‖≤_
    rw [MixedJointUncutMark.cutoff_mark_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base (u q.2)) hδ]
    by_cases hg : CutoffUncutComparison.Active (Base (u q.2)) δ k q.1
    · simpa only [hg,ite_true] using hK (u q.2) q.1 q.2
    · simp only [hg,ite_false,norm_zero]
      exact mul_nonneg hKn (UncutSmoothWords.weight_nonneg (Base (0,0)) k q.1)
  · intro q
    exact MixedJointUncutMark.mark_eventually_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base (u q.2)) k q.1 q.2

end SHE.ControlledReferenceRandomMarkLimit
