module

public import SHE.MixedNamedBackwardStep
public import SHE.MixedNativeJointPhysical

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.MixedNamedPhysicalStep
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open SmoothCylinders FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open GaussianItoTest GaussianTaylorAverage CovarianceEndpoint
open scoped NNReal ENNReal
local instance nativeJointPhysicalStep_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativeJointPhysicalStep_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointPhysicalStep_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointPhysicalStep_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointPhysicalStep_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointPhysicalStep_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointPhysicalStep_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

include hIJ₀ hIJ₁ in
/-- The literal local-insertion/first-defect step for the constructed
native pair. Only the local scalar coefficient is appended as aU new
point leaf; the full common-Haar defect is retained as aU terminating
mark. Original stops and targets are not identified. -/
theorem formula (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    {n : ℕ} (W : EndpointWindow n) (hleft : 0≤W.left)
    (b : ℝ≥0) (hW : W.right=(b:ℝ)) (hbH : b≤H)
    {δ : ℝ} (hδ : 0<δ) (hgap : ∀ i,δ≤(W.observations i).target-(b:ℝ))
    (hstop : ∀ i,(b:ℝ)≤(W.observations i).stop)
    {F : State n→ℝ} (hF : BoundedSmooth F) :
    let Y := fun (ω : Ω) (t : ℝ) => MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      W.observations b t.toNNReal ω
    let strictGap:∀i,(b:ℝ)<(W.observations i).target:=by intro i; have hh:=hgap i; linarith
    let N:=MixedJointNamedIto.scalarNoise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      J hIJ₀ hIJ₁ hnull hΛ W.observations b strictGap hbH W.left.toNNReal (backward W F)
    ∀ᵐ ω ∂μ,
      F (Y ω b)=WordRecursion.gaussianSemigroup W.coefficient W.observations W.left W.right F (Y ω W.left)+N ω+
        ∫ t in W.left..W.right,
          (∫ x : HeatCircle,WordRecursion.insertion (fun v => κ+aV v) W.coefficient W.observations t x (backward W F t)
            (JointPhysicalInsertion.appendState
              (PredictableScalarField.wordField (Function.uncurry S.second) ω (t,x)) (Y ω t)) ∂AddCircle.haarAddCircle)+
          (1/2:ℝ)*covarianceAction
            (MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W.observations (t.toNNReal,ω))
            (GaussianTaylor.hessian (backward W F t) (Y ω t)) := by
  intro Y strictGap N
  have hl:W.left=(W.left.toNNReal:ℝ):=(Real.coe_toNNReal W.left hleft).symm
  have hN:=MixedNamedBackwardStep.formula 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hnull hJ hΛ W W.left.toNNReal hl b hW hbH strictGap hF
  have hΓ := MixedNativeJointCovariance.rowCovariance_eq_total_add_defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S W.observations hΛ b hδ hgap
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hA : 0≤κ+M := add_nonneg hκ.le hM
  have hbound : ∀ z,|κ+aV z|≤κ+M := by
    intro z
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbV z).1))]
    exact add_le_add le_rfl (hbV z).2
  filter_upwards [hN,hΓ] with ω hω hΓ
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le W.ordered,← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hs : Ioo W.left W.right ⊆ Ioc (0:ℝ) (H:ℝ) := by
    intro t ht
    exact ⟨hleft.trans_lt ht.1,ht.2.le.trans (by rw [hW];exact_mod_cast hbH)⟩
  have hΓ' := hΓ.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  filter_upwards [hΓ',ae_restrict_mem measurableSet_Ioo] with t ht htm
  have htb : t<(b:ℝ) := by rw [← hW];exact htm.2
  rw [ht htb]
  exact (MixedNativeJointBackwardStep.cancellation W F _ t (Y ω t)).symm.trans
    (JointPhysicalInsertion.insertion_and_defect W (fun v => κ+aV v) (measurable_const.add haV)
      (PredictableScalarField.wordField (Function.uncurry S.second) ω)
      (PredictableScalarField.wordField_section_measurable 𝓕 S.second_predictable ω)
      hA hbound F htm (Y ω t) _)

end SHE.MixedNamedPhysicalStep
