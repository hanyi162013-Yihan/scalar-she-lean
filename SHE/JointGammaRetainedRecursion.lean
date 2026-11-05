module

public import SHE.JointGammaEndpointDrift
public import SHE.FiniteItoParameterResidual
public import SHE.JointGammaRecursionRows
public import SHE.JointGammaRecursionState
public import SHE.ControlledReferenceLevel
public import SHE.MixedJointUncutMark
public import SHE.ActualUncutRemainder
public import SHE.FirstGammaEndpointMappedRows
public import SHE.JointGammaDriftAlgebra
public import SHE.JointGammaTestFields
public import SHE.FiniteReferenceSpliceRows
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaEndpointCovariance
public import SHE.FiniteAffineRows
public import SHE.PredictableRealSections
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.JointGammaRetainedRecursion
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointDrift_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointDrift_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointDrift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointDrift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointDrift_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointDrift_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointDrift_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointDrift_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


open Set FiniteCovariancePullback SmoothCylinders GaussianConvolution GaussianItoTest
variable (hvb:v≤b)(hstop:∀ i,(Z i).stop=(Z i).target)
variable {F:WordRecursion.State n→ℝ}(hF:BoundedSmooth F)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Past"=>MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "hs"=>(fun i=>(htarget i).trans_eq (hstop i).symm)
local notation "Level" θ:max p:max=>ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hs F hF p
local notation "W" θ:max p:max=>ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "Y" θ:max=>FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ
local notation "Rows" θ:max=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "G" θ:max=>JointGammaTestFields.value P Λ θ v b hvb Z htarget F
local notation "dG" θ:max=>JointGammaTestFields.derivative P Λ θ v b hvb Z htarget F
local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "StateJ"=>MixedNativeJointHistory.evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z
local notation "Defect"=>MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z

def retained (θ:ℝ)(ω:Ω):ℝ:=∫t in (v:ℝ)..(b:ℝ),
  FiniteItoParameterResidual.drift (Y θ) (StandardFiniteIto.rowCovariance 𝓕 μ H (Rows θ))
    (G θ) (dG θ) (Past ω) ω t

include hH B hBDG hIJ₀ hIJ₁ in
/-- The actual theta-one retained drift is precisely the depth-zero
joint local remainder and full uncut first-defect mark. -/
theorem one_eq_mark_remainder(hb0:0<b):∀ᵐω∂μ,
    retained (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb 1 ω=
      MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S (Level 1 (Past ω)) () ω+
      MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S (Level 1 (Past ω)) 0 () ω:=by
  have hd:=JointGammaEndpointDrift.actual_drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 1 hvb hF
  have hr:=PredictableRealSections.of_energy_ae μ H
    (JointGammaRecursionRows.one_gram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH hstop)
    v b v.2 (by exact_mod_cast hvb) (by exact_mod_cast hbH)
  have hy:=PredictableRealSections.of_energy_ae μ H
    (JointGammaRecursionState.one_eq_joint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hH B hBDG hIJ₀ hIJ₁ hb0 hstop)
    v b v.2 (by exact_mod_cast hvb) (by exact_mod_cast hbH)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hcap(z):|κ+aV z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbV z).1))]
    exact add_le_add le_rfl (hbV z).2
  filter_upwards [hd,hr,hy] with ω hd hr hy
  have hR:=JointInsertionIntegrability.time_integrable (Level 1 (Past ω)) Λ
    (DU).physicalState_measurable (DV).physicalState_measurable
    (DU).physicalField_measurable (DV).physicalField_measurable () ω
  obtain ⟨K,hK,hmark⟩:=MixedJointLevelData.mark_uniform_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S (Level 1 (Past ω)) hΛ
  have hMark:MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S (Level 1 (Past ω)) 0 () ω=
      MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S (Level 1 (Past ω)) () ω:=by
    simp only [MixedJointUncutMark.mark,UncutSmoothWords.weight,one_mul]
    rfl
  rw [hMark,retained,MixedJointLevelData.localRemainder,MixedJointLevelData.mark,
    JointWordAnalytic.remainder,JointWordDefect.mark,←intervalIntegral.integral_add hR (hmark () ω).2]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)]
  filter_upwards [hd,hr,hy,ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t hd hr hy ht hne
  have ht0:0≤t:=v.2.trans ht.1.le
  have htb:t<(b:ℝ):=lt_of_le_of_ne ht.2 hne
  have hvq:v<t.toNNReal:=by exact_mod_cast (show (v:ℝ)<(t.toNNReal:ℝ) by rw [Real.coe_toNNReal _ ht0];exact ht.1)
  have hqb:t.toNNReal<b:=by exact_mod_cast (show (t.toNNReal:ℝ)<(b:ℝ) by rw [Real.coe_toNNReal _ ht0];exact htb)
  have hy':JointGammaAffine.current n Λ 1 (fun i=>(Z i).target) ((Y 1) (t.toNNReal,ω))=
      StateJ ω t:=by simpa only [Real.coe_toNNReal _ ht0] using hy hvq hqb
  change FiniteItoParameterResidual.drift (Y 1) (StandardFiniteIto.rowCovariance 𝓕 μ H (Rows 1))
      (G 1) (dG 1) (Past ω) ω t=_
  rw [FiniteItoParameterResidual.drift,hd,hr hvq hqb,hy']
  have hX:Measurable (fun tx=>(DV).physicalField (ω,tx)):=
    (DV).physicalField_measurable.comp (measurable_const.prodMk measurable_id)
  have hh:=JointGammaDriftAlgebra.insertion_defect (W 1 (Past ω)) (fun z=>κ+aV z)
    (measurable_const.add haV) (fun tx=>(DV).physicalField (ω,tx)) hX
    (add_nonneg hκ.le hM) hcap F (show t∈Ioo (W 1 (Past ω)).left (W 1 (Past ω)).right from ⟨ht.1,htb⟩)
    (StateJ ω t) _ (Defect (t.toNNReal,ω)) rfl
  simpa only [Real.coe_toNNReal _ ht0,JointWordAnalytic.insertion,JointWordAnalytic.state,
    JointWordDefect.integrand,JointWordHessian.field,MixedJointLevelData.defect,
    ControlledReferenceLevel.window_eq,CutoffWordLevel.Level.window,ControlledReferenceLevel.level,ControlledReferenceLevel.referenceData,
    ControlledReferenceWindows.window,MixedNativeJointHistory.evaluate,MixedNativeJointHistory.secondData,
    PredictableWordState.Data.physicalField,GaussianItoTest.backward] using hh
end SHE.JointGammaRetainedRecursion
