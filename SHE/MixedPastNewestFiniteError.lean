module
public import SHE.MixedPastNewestApproximation
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
namespace SHE.MixedPastNewestFiniteError
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement ControlledOldIntervals MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestFiniteError_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestFiniteError_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestFiniteError_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestFiniteError_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestFiniteError_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestFiniteError_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestFiniteError_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestFiniteError_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestFiniteError_period : Fact (0<2*π):=⟨by positivity⟩
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

open scoped Topology

/-- The original finite-depth expansion uses unit coefficients. Signed
unit weights also cover subtracting its two endpoint expansions. Every
factor 1/2 remains in the actual recursive word and newest insertion. -/
def field (D:SmoothApproximation.ScalarData)(j depth:ℕ)(w:ℕ→ℝ)(z:HeatCircle×Ω):ℝ:=
  ∑k∈Finset.range depth,w k*MixedPastNewestIntegratedError.drift
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 0
      (MixedPastNewestIntegratedError.coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j) z

def constant (Q:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)
    (depth:ℕ)(B0:ℕ→ℝ≥0)(A0 ν:ℝ):ℝ:=
  (depth:ℝ)*(∑k∈Finset.range depth,MixedPastNewestCurrentEnergy.constant κ (M:=M) Q v b B Hr k (B0 k) A0 ν*
    (((b:ℝ)-(v:ℝ))^(Q.exponent/8)/(Q.exponent/8))^2)

theorem budget_tendsto (D:SmoothApproximation.ScalarData)(Q:CanonicalCovariance.ProfileParameters)
    (κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)(depth:ℕ)(B0:ℕ→ℝ≥0)(A0 ν:ℝ):
    Filter.Tendsto (fun j=>(ScalarApproximationDiscrepancy.scalarError D j)^2*
      constant Q κ M v b B Hr depth B0 A0 ν) Filter.atTop (𝓝 (0:ℝ)):=by
  simpa only [zero_pow (by norm_num : 2≠0),zero_mul] using
    ((MixedPastNewestApproximation.scalarError_tendsto D).pow 2).mul_const
      (constant Q κ M v b B Hr depth B0 A0 ν)

/-- This index is chosen from numerical data before any actual
companion process, initial state, root field, or Gaussian derivative
bound. It therefore remains valid when all those objects vary with j. -/
def threshold (D:SmoothApproximation.ScalarData)(Q:CanonicalCovariance.ProfileParameters)
    (κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)(depth:ℕ)(B0:ℕ→ℝ≥0)(A0 ν δ:ℝ)(hδ:0<δ):ℕ:=
  Classical.choose (Filter.eventually_atTop.1
    ((budget_tendsto D Q κ M v b B Hr depth B0 A0 ν).eventually (gt_mem_nhds hδ)))

theorem threshold_bound (D:SmoothApproximation.ScalarData)(Q:CanonicalCovariance.ProfileParameters)
    (κ M:ℝ)(v b:ℝ≥0)(B Hr:ℝ)(depth:ℕ)(B0:ℕ→ℝ≥0)(A0 ν δ:ℝ)(hδ:0<δ)
    (j:ℕ)(hj:threshold D Q κ M v b B Hr depth B0 A0 ν δ hδ≤j):
    (ScalarApproximationDiscrepancy.scalarError D j)^2*
      constant Q κ M v b B Hr depth B0 A0 ν<δ:=
  Classical.choose_spec (Filter.eventually_atTop.1
    ((budget_tendsto D Q κ M v b B Hr depth B0 A0 ν).eventually (gt_mem_nhds hδ))) j hj

include hIJ₀ hIJ₁ in
/-- Actual finite sum of all ordinary U-side approximation-error
insertions. The common constant is independent of the smoothing index
and includes every old/current collision, with no time cutoff. -/
theorem energy (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)
    (j:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall j)
    {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(hvb':v<b)(hbH:b≤H)(depth:ℕ)
    (hold:∀i,i<depth→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 i)
    (A0 ν:ℝ)(hA:0≤A0)(hν:0≤ν)
    (hjet:∀x i,i≤depth→∀z,‖iteratedFDeriv ℝ i (F x) z‖≤A0*ν^i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k))
    (w:ℕ→ℝ)(hw:∀k,k<depth→|w k|≤1):
    Integrable (fun z:HeatCircle×Ω=>|field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm D j depth w z|^2) (haarAddCircle.prod μ) ∧
    (∫z:HeatCircle×Ω,|field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm D j depth w z|^2 ∂haarAddCircle.prod μ)≤
      (ScalarApproximationDiscrepancy.scalarError D j)^2*
        constant (ControlledSmoothLimit.roughTotalParameters D hh hh1 hsmall) κ M v b B Hr depth B0 A0 ν:=by
  let Q:=ControlledSmoothLimit.roughTotalParameters D hh hh1 hsmall
  let err:=MixedPastNewestIntegratedError.coefficientError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j
  let E:=fun k=>MixedPastNewestIntegratedError.drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k 0 err
  let ε:=ScalarApproximationDiscrepancy.scalarError D j
  have hem:Measurable err:=MixedPastNewestIntegratedError.coefficientError_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D j
  have hEm(k:ℕ):Measurable (E k):=
    (MixedPastNewestIntegratedError.integrand_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 0 err hem).stronglyMeasurable.integral_prod_left'.measurable
  have he(k:ℕ)(hk:k∈Finset.range depth):
      Integrable (fun z:HeatCircle×Ω=>|E k z|^2) (haarAddCircle.prod μ) ∧
      (∫z:HeatCircle×Ω,|E k z|^2 ∂haarAddCircle.prod μ)≤
        MixedPastNewestApproximation.budget D Q κ M v b B Hr k (B0 k) A0 ν j:=by
    have hkd:k<depth:=Finset.mem_range.mp hk
    exact MixedPastNewestApproximation.canonical_energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
      D hh hh1 hsmall j hP hB hHr hroot hrootmod hlocal hΛ hages hrootStop hrootTarget
      hspan hvb' hbH k (fun i hi=>hold i (hi.trans hkd)) A0 ν hA hν
      (fun x i hi=>hjet x i (hi.trans hkd.le)) (B0 k) (hBDG k hkd)
  let G:=field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm D j depth w
  have hGm:Measurable G:=Finset.measurable_sum _ (fun k _=>measurable_const.mul (hEm k))
  have hpoint(z:HeatCircle×Ω):|G z|^2≤(depth:ℝ)*(∑k∈Finset.range depth,|E k z|^2):=by
    have hc:=sq_sum_le_card_mul_sum_sq (s:=Finset.range depth) (f:=fun k=>w k*E k z)
    simp only [Finset.card_range] at hc
    rw [sq_abs]
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro k hk
    have hwk:=hw k (Finset.mem_range.mp hk)
    have hab:|w k*E k z|≤|E k z|:=by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hwk (abs_nonneg _)).trans_eq (one_mul _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
  have hsum:Integrable (fun z:HeatCircle×Ω=>∑k∈Finset.range depth,|E k z|^2) (haarAddCircle.prod μ):=
    integrable_finsetSum _ (fun k hk=>(he k hk).1)
  have hGi:Integrable (fun z:HeatCircle×Ω=>|G z|^2) (haarAddCircle.prod μ):=
    (hsum.const_mul (depth:ℝ)).mono' (hGm.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun z=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (|G z|))]
        exact hpoint z))
  refine ⟨hGi,?_⟩
  have hb:=(integral_mono hGi (hsum.const_mul (depth:ℝ)) hpoint)
  rw [integral_const_mul,integral_finsetSum _ (fun k hk=>(he k hk).1)] at hb
  apply hb.trans
  have hs:=Finset.sum_le_sum (fun k hk=>(he k hk).2)
  have ht:=mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg depth : (0:ℝ)≤depth)
  apply ht.trans_eq
  have hx:(∑k∈Finset.range depth,MixedPastNewestApproximation.budget D Q κ M v b B Hr k (B0 k) A0 ν j)=
      ε^2*(∑k∈Finset.range depth,MixedPastNewestCurrentEnergy.constant κ (M:=M) Q v b B Hr k (B0 k) A0 ν*
        (((b:ℝ)-(v:ℝ))^(Q.exponent/8)/(Q.exponent/8))^2):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [MixedPastNewestApproximation.budget,ε]
    ring
  rw [hx]
  dsimp only [constant,Q,ε]
  ring

include hIJ₀ hIJ₁ in
/-- A single deterministic smoothing index makes the actual full
finite expansion error small, uniformly over varying companion models
and root fields satisfying the stated common finite-jet bounds. -/
theorem energy_small (D:SmoothApproximation.ScalarData){h:ℝ}(hh:0<h)(hh1:h≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*h^(D.beta/4)≤1/2)
    (j:ℕ)(hP:P=ControlledSmoothLimit.smoothTotalParameters D hh hh1 hsmall j)
    {B Hr:ℝ}(hB:0≤B)(hHr:0≤Hr)
    (hroot:∀x z,|F x z|≤B)
    (hrootmod:∀x z w,|F x z-F x w|≤Hr*|z 0-w 0|^P.exponent)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(hvb':v<b)(hbH:b≤H)(depth:ℕ)
    (hold:∀i,i<depth→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 i)
    (A0 ν:ℝ)(hA:0≤A0)(hν:0≤ν)
    (hjet:∀x i,i≤depth→∀z,‖iteratedFDeriv ℝ i (F x) z‖≤A0*ν^i)
    (B0:ℕ→ℝ≥0)(hBDG:∀k,k<depth→StandardTerminalBDGPower (k+2) J (B0 k))
    (w:ℕ→ℝ)(hw:∀k,k<depth→|w k|≤1)
    (δ:ℝ)(hδ:0<δ)
    (hj:threshold D (ControlledSmoothLimit.roughTotalParameters D hh hh1 hsmall)
      κ M v b B Hr depth B0 A0 ν δ hδ≤j):
    (∫z:HeatCircle×Ω,|field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm D j depth w z|^2 ∂haarAddCircle.prod μ)<δ:=by
  exact (energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm D hh hh1 hsmall j hP hB hHr hroot hrootmod
    hlocal hΛ hages hrootStop hrootTarget hspan hvb' hbH depth hold A0 ν hA hν hjet B0 hBDG w hw).2.trans_lt
      (threshold_bound D _ κ M v b B Hr depth B0 A0 ν δ hδ j hj)

end SHE.MixedPastNewestFiniteError
