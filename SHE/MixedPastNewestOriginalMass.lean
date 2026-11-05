module
public import SHE.MixedPastNewestIntegratedError
public import SHE.ControlledNewestNodeMass
public import SHE.RootSectionAverage
public import SHE.NewestIntegratedConstants
public import SHE.MixedPastNewestTimeFields
public import SHE.NewestErrorConstants
public import SHE.ScalarApproximationDiscrepancy
public import SHE.PastNewestOldTimeEnergy
public import SHE.MixedPastNewestFields
public import SHE.ParentScoreInput
public import SHE.ParentMeanMass
public import SHE.WeightedSFiniteMoments
public import SHE.PastWordTimeFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.MixedPastNewestOriginalMass
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestOriginalMass_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestOriginalMass_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestOriginalMass_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestOriginalMass_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestOriginalMass_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestOriginalMass_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestOriginalMass_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestOriginalMass_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestOriginalMass_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MixedPastNewestError.value WordRecursion.directionalSecond
  GaussianConvolution.gaussianAverage UncutSmoothWords.test MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Value"=>MixedPastNewestError.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

open HistoryProductMeasure OrderedHeatForests
open ActualMeanKernel
local notation "Active"=>MixedPastNewestFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "U"=>MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir"=>MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def current (k:ℕ)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(z:ℝ×(Ω×History HeatCircle k)):ℝ:=
  MixedPastNewestTimeFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k e ((0,(z.1.toNNReal,z.2.1)),z.2.2)

def primitive (k:ℕ)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(z:Ω×History HeatCircle k):ℝ:=
  ∫q,current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k e (q,z) ∂volume.restrict (Ioc (v:ℝ) (b:ℝ))

theorem current_measurable (k:ℕ)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(he:Measurable e):
    Measurable (current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k e):=by
  exact (MixedPastNewestTimeFields.active_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k e he).comp
      ((measurable_const.prodMk ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

/-- Absolute integrability BEFORE original current-time/history Fubini.
The proof uses a fixed-smooth-index coarse successor weight only; it
places no derivative-dependent restriction on the uniform diagonal. -/
theorem joint_integrable
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (k:ℕ)(ε:ℝ)(hε:0≤ε)(e:(ℝ≥0×Ω)×HeatCircle→ℝ)(he:Measurable e)(hecap:∀p,|e p|≤ε):
    Integrable (current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k e)
      ((volume.restrict (Ioc (v:ℝ) (b:ℝ))).prod (μ.prod (historyMeasure R₀ haarAddCircle k))):=by
  let σ:=historyMeasure R₀ (haarAddCircle:Measure HeatCircle) k
  let τ:Measure ℝ:=volume.restrict (Ioc (v:ℝ) (b:ℝ))
  let g:History HeatCircle k×ℝ→ℝ:=fun z=>∫y,UncutSmoothWords.weight Zero (k+1) (z.1,(z.2,y)) ∂haarAddCircle
  have hwm:=UncutSmoothWords.weight_measurable Zero (k+1)
  have hgm:Measurable g:=
    (hwm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable
  have hwi:Integrable (fun z:History HeatCircle k×(ℝ×HeatCircle)=>UncutSmoothWords.weight Zero (k+1) z)
      (σ.prod (τ.prod haarAddCircle)):=UncutHistoryMass.weight_integrable Zero haarAddCircle (k+1)
  have hAssoc:=measurePreserving_prodAssoc σ τ (haarAddCircle:Measure HeatCircle)
  have hAssocm:Measurable (fun z:(History HeatCircle k×ℝ)×HeatCircle=>(z.1.1,(z.1.2,z.2))):=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hgi:Integrable g (σ.prod τ):=
    ((hAssoc.integrable_comp hwm.aestronglyMeasurable).mpr hwi).integral_prod_left
  have hbig:Integrable (fun z:Ω×(ℝ×History HeatCircle k)=>g (z.2.2,z.2.1)) (μ.prod (τ.prod σ)):=
    hgi.swap.comp_snd μ
  have hbigm:Measurable (fun z:Ω×(ℝ×History HeatCircle k)=>g (z.2.2,z.2.1)):=
    hgm.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  have hp:MeasurePreserving (fun z:ℝ×(Ω×History HeatCircle k)=>(z.2.1,(z.1,z.2.2)))
      (τ.prod (μ.prod σ)) (μ.prod (τ.prod σ)):=by
    exact (measurePreserving_prodAssoc μ τ σ).comp
      (((Measure.measurePreserving_swap (μ:=τ) (ν:=μ)).prod (MeasurePreserving.id σ)).comp
        (measurePreserving_prodAssoc τ μ σ).symm)
  have hmajor:Integrable (fun z:ℝ×(Ω×History HeatCircle k)=>g (z.2.2,z.1)) (τ.prod (μ.prod σ)):=
    (hp.integrable_comp hbigm.aestronglyMeasurable).mpr hbig
  obtain ⟨C,hC,hCb⟩:=ControlledNewestNodeMass.bound P P.coefficient haP Λ 0 v b hvb Z htarget hstop F hF hFm hages k
  have hFm':=current_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k e he
  have hbound:∀ᵐq∂τ,∀z:Ω×History HeatCircle k,
      |current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k e (q,z)|≤C*ε*g (z.2,q):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    intro z
    have hq0:0≤q:=v.2.trans hq.1.le
    have hqNN:(q.toNNReal:ℝ)=q:=Real.coe_toNNReal q hq0
    unfold current MixedPastNewestTimeFields.active
    dsimp only
    by_cases hqt:q<(carrier Zero k).terminal z.2
    · rw [if_pos (by simpa only [hqNN] using hqt)]
      have hef:Measurable (fun y:HeatCircle=>e ((q.toNNReal,z.1),y)):=he.comp (measurable_const.prodMk measurable_id)
      have hb:=hCb (U z.1,Dir z.1) z.2 q hq.1 hqt (Mean k 0 q.toNNReal z.1 z.2) ε hε
        (fun y=>e ((q.toNNReal,z.1),y)) hef (fun _=>hecap _)
      simpa only [MixedPastNewestError.value,hqNN,g] using hb.2
    · rw [if_neg (by simpa only [hqNN] using hqt)]
      simp only [abs_zero]
      exact mul_nonneg (mul_nonneg hC hε)
        (integral_nonneg (fun _=>UncutSmoothWords.weight_nonneg _ _ _))
  have hset:MeasurableSet {z:ℝ×(Ω×History HeatCircle k)|
      |current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k e z|≤C*ε*g (z.2.2,z.1)}:=
    measurableSet_le (continuous_abs.measurable.comp hFm')
      (measurable_const.mul (hgm.comp (measurable_snd.snd.prodMk measurable_fst)))
  have hAE:∀ᵐz∂τ.prod (μ.prod σ),
      |current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k e z|≤C*ε*g (z.2.2,z.1):=
    (Measure.ae_prod_iff_ae_ae hset).mpr
    (hbound.mono (fun q h=>ae_of_all _ h))
  apply (hmajor.const_mul (C*ε)).mono' hFm'.aestronglyMeasurable
  filter_upwards [hAE] with z hz
  simpa only [Real.norm_eq_abs] using hz

end SHE.MixedPastNewestOriginalMass
