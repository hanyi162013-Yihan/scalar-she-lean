module

public import SHE.JointGammaRetainedRecursion
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

namespace SHE.JointGammaOrdinaryRetained
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
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

include hH B hBDG hIJ₀ hIJ₁ in
/-- The theta-zero retained drift uses the actual ordinary-U bracket,
with the companion coefficient still only in its smooth word reference. -/
theorem zero_eq_actual_remainder(hb0:0<b):∀ᵐω∂μ,
    JointGammaRetainedRecursion.retained (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb 0 ω=
    ActualUncutRemainder.value (Level 0 (Past ω)) (fun z=>κ+aU z)
      (DU).physicalState (DU).physicalField 0 () ω:=by
  have hd:=JointGammaEndpointDrift.actual_drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH 0 hvb hF
  have hr:=PredictableRealSections.of_energy_ae μ H
    (JointGammaRecursionRows.zero_gram 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH)
    v b v.2 (by exact_mod_cast hvb) (by exact_mod_cast hbH)
  have hy:=PredictableRealSections.of_energy_ae μ H
    (JointGammaRecursionState.zero_eq_ordinary 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hH B hBDG hIJ₀ hIJ₁ hb0)
    v b v.2 (by exact_mod_cast hvb) (by exact_mod_cast hbH)
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hcap(z):|κ+aU z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbU z).1))]
    exact add_le_add le_rfl (hbU z).2
  filter_upwards [hd,hr,hy] with ω hd hr hy
  simp only [ActualUncutRemainder.value,UncutSmoothWords.weight,one_mul]
  change (∫t in (v:ℝ)..(b:ℝ),FiniteItoParameterResidual.drift (Y 0)
      (StandardFiniteIto.rowCovariance 𝓕 μ H (Rows 0)) (G 0) (dG 0) (Past ω) ω t)=
    PhysicalIto.wordRemainder (W 0 (Past ω)) (fun z=>κ+aU z)
      (fun t=>(DU).physicalState (ω,t)) (fun tx=>(DU).physicalField (ω,tx)) F
  rw [PhysicalIto.wordRemainder]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)]
  filter_upwards [hd,hr,hy,ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t hd hr hy ht hne
  have ht0:0≤t:=v.2.trans ht.1.le
  have htb:t<(b:ℝ):=lt_of_le_of_ne ht.2 hne
  have hvq:v<t.toNNReal:=by exact_mod_cast (show (v:ℝ)<(t.toNNReal:ℝ) by rw [Real.coe_toNNReal _ ht0];exact ht.1)
  have hqb:t.toNNReal<b:=by exact_mod_cast (show (t.toNNReal:ℝ)<(b:ℝ) by rw [Real.coe_toNNReal _ ht0];exact htb)
  have hy':JointGammaAffine.current n Λ 0 (fun i=>(Z i).target) ((Y 0) (t.toNNReal,ω))=
      WordRecursion.observe (fun s=>(DU).physicalState (ω,s)) (fun tx=>(DU).physicalField (ω,tx)) Z t:=by
    simpa only [Real.coe_toNNReal _ ht0] using hy hvq hqb
  rw [FiniteItoParameterResidual.drift,hd,hr hvq hqb,hy']
  have hX:Measurable (fun tx=>(DU).physicalField (ω,tx)):=
    (DU).physicalField_measurable.comp (measurable_const.prodMk measurable_id)
  have hh:=JointGammaDriftAlgebra.insertion_defect (W 0 (Past ω)) (fun z=>κ+aU z)
    (measurable_const.add haU) (fun tx=>(DU).physicalField (ω,tx)) hX
    (add_nonneg hκ.le hM) hcap F (show t∈Ioo (W 0 (Past ω)).left (W 0 (Past ω)).right from ⟨ht.1,htb⟩)
    (WordRecursion.observe (fun s=>(DU).physicalState (ω,s)) (fun tx=>(DU).physicalField (ω,tx)) Z t)
    _ 0 (add_zero _).symm
  simp only [GaussianTaylorAverage.covarianceAction,Matrix.zero_apply,zero_mul,Finset.sum_const_zero,
    mul_zero,add_zero] at hh
  have he:(∫y:HeatCircle,WordRecursion.insertion (fun z=>κ+aU z) (W 0 (Past ω)).coefficient Z t y
    (backward (W 0 (Past ω)) F t)
    (JointPhysicalInsertion.appendState ((DU).physicalField (ω,(t,y)))
      (WordRecursion.observe (fun s=>(DU).physicalState (ω,s)) (fun tx=>(DU).physicalField (ω,tx)) Z t))
    ∂AddCircle.haarAddCircle)=
    ∫y:HeatCircle,PhysicalIto.insertedWord (W 0 (Past ω)) (fun z=>κ+aU z)
      (fun s=>(DU).physicalState (ω,s)) (fun tx=>(DU).physicalField (ω,tx)) F t y
      ∂AddCircle.haarAddCircle:=by
    apply integral_congr_ae
    filter_upwards with y
    rw [PhysicalIto.insertedWord,WordRecursion.insertion_observe,JointPhysicalInsertion.insertion_appendState]
    rfl
  have hhfinal:=hh.trans he
  simpa only [GaussianTaylorAverage.covarianceAction,Real.coe_toNNReal _ ht0,ControlledReferenceWindows.window,
  MixedNativeJointHistory.firstData,PredictableWordState.Data.physicalField,GaussianItoTest.backward] using hhfinal

end SHE.JointGammaOrdinaryRetained
