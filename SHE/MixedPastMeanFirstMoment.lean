module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.ControlledFamilyMeanFirstMoment
public import SHE.PastMeanAbsoluteBudget

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanFirstMoment
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanFirstMoment_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanFirstMoment_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanFirstMoment_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanFirstMoment_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanFirstMoment_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanFirstMoment_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanFirstMoment_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanFirstMoment_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanFirstMoment_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)

/-- The entire native negative-output mean mark, applied to the actual
dependent current difference of the original mixed common-driver pair. -/
def input (k : ℕ) (θ : ℝ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ω : Ω) : CircleL2 :=
  OneInputOperator.besselHalf mass ρ hmass hρ
    (integralOperator (MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q q t) ω
      (embed (S.second q ω-S.first q ω)))

attribute [local irreducible] cappedAverage weightedPoint MixedPastLiteralPoint.meanField

/-- Actual native current-mean derivative at each original history,
before any old-space cancellation. -/
def value (k : ℕ) (θ : ℝ) (q : ℝ≥0) (p : History HeatCircle k) (ω : Ω) : ℝ :=
  fderiv ℝ (cappedAverage (Base (θ,(U ω,Dir ω))) k q p) (Mean k θ q ω p)
    (PhysicalMeanRange.dampedDirection
      (fun i=>((carrier Zero k).observations.observations p i).stop)
      (fun i=>((carrier Zero k).observations.observations p i).target)
      (fun i=>NativeHeatSpan.unitCenter ((carrier Zero k).observations.observations p i).center)
      q Λ (embed (S.second q ω-S.first q ω)))

include hIJ₀ hIJ₁ in
/-- The complete correlated mean leg has an absolute first moment at
almost every ORIGINAL history. The positive parent density is retained
unsquared, so subsequent old-space integration uses its true mass. -/
theorem first_moment_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target≤(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (root : Measure HeatCircle) [IsFiniteMeasure root] (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (θ : ℝ) (hθ : |θ|≤1) (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    let C:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    ∀ᵐ p ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) root k,
      StrictHistory Zero k p → (q:ℝ)<(carrier Zero k).terminal p →
      Integrable (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q p) μ ∧
      (∫ ω,|value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q p ω| ∂μ)≤
        sqrt (∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)*
          (sqrt C*((1+k:ℕ):ℝ)*sqrt (2*UniformFutureProfileScores.constant (1+k)/P.lower))*
          PastMeanTimeFactors.absoluteDensity Zero P (fraction P*P.lower) (uniformConstant 1) k q (1/2:ℝ) A0 ν p := by
  intro C
  let a : Ω→ℝ×Inputs:=fun ω=>(θ,(U ω,Dir ω))
  let m:=Mean k θ q
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have ha : Measurable a:=measurable_const.prodMk (hU.prodMk hDir)
  have hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2):=
    MixedPastLiteralFields.meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q
  have hV0:=MixedHeatedDifferenceMoments.difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q
  have hV : Measurable (fun ω=>embed (S.second q ω-S.first q ω)):=embed.continuous.measurable.comp hV0
  have hVi0:=(MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hq1 (k+2) (by omega) B0 hBDG).1
  have hVi : Integrable (fun ω=>‖embed (S.second q ω-S.first q ω)‖^2) μ:=by simpa only [embed_norm] using hVi0
  have hC : 0≤C:=MixedPastWordMoments.momentConstant_nonneg P k k 1 _
  have hpall:=MixedPastLiteralPoint.conditional_even_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hages hrootStop hspan root k
  filter_upwards [hpall] with p hp
  intro hstrict hqt
  let W:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k p
  let G:=PastWordTimeFields.total Zero P k p A0 ν
  let D0:=sqrt (2*UniformFutureProfileScores.constant (1+k)/(P.lower*((carrier Zero k).terminal p-q)))*W*G
  have hW : 0≤W:=timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
    (fun j=>(uniformConstant_pos 1 j).le) k p hstrict
  have hG : 0≤G:=PastWordTimeFields.total_nonneg Zero P k p A0 ν
  have htotal : PastWordTimeFields.total Zero P k p A0 ν=
      MixedPastWordMoments.total (d:=1) P (fun j=>lower Zero k p j-(v:ℝ))
        (fun j=>upper Zero k p j-(v:ℝ))
        (fun j=>targets Zero k p (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν := rfl
  have hD0 : 0≤D0:=mul_nonneg (mul_nonneg (sqrt_nonneg _) hW) hG
  have hsmall : SmallHistory Zero (uniformHorizon 1) k p :=
    RelativeHistoryGeometry.smallHistory_of_span Zero (b:ℝ) (fun _=>le_rfl) hrootTarget
      (uniformHorizon 1) k hold p
  have hsmallf (i) : targets Zero k p i-q≤UniformFutureProfileScores.horizon (1+k) :=
    (RelativeHistoryGeometry.carrier_age_le_span Zero (b:ℝ) (fun _=>le_rfl) hrootTarget k p
      (by exact_mod_cast hvq) i).trans hfresh
  have hy:=hp q hvq hqH hqt q le_rfl hqt hsmallf hstrict hsmall θ hθ A0 ν hA0 hν
    (hjet (rootParameter k p)) 1 (by norm_num) B0 (by simpa using hBDG)
  have hpoint : ∀ᵐ y ∂haarAddCircle,
      Integrable (fun ω=>|weightedPoint (Base (a ω)) k Λ q q (m ω) p y|^2) μ ∧
      (∫ ω,|weightedPoint (Base (a ω)) k Λ q q (m ω) p y|^2 ∂μ)≤
        C*(D0*ParentMeanDensity.globalDensity Zero k p q y)^2 := by
    filter_upwards [hy] with y hy
    have hh:=hy univ MeasurableSet.univ
    have hprod:=ParentMeanDensity.parentProduct_eq_parentDensity Zero hages k p hstrict
    have hprod' : ParentMeanDensity.parentProduct Zero k p=
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k p)
          (carrier_orderedTimes Zero hages k p hstrict) (centers Zero k p):=hprod
    have hglobal : ParentMeanDensity.globalDensity Zero k p q y=
        ParentMeanDensity.parentProduct Zero k p*
          ∑ i,Real.sqrt ‖ProfileVariance.heatPhysical (4*(targets Zero k p i-(q:ℝ))) (centers Zero k p i) y‖:=rfl
    have heq :
        (timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k p*
          OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k p)
            (carrier_orderedTimes Zero hages k p hstrict) (centers Zero k p))*
        (exp (-Λ*((q:ℝ)-(q:ℝ)))*sqrt (2*UniformFutureProfileScores.constant (1+k)/
          (P.lower*((carrier Zero k).terminal p-(q:ℝ))))*
            ∑ i,Real.sqrt ‖ProfileVariance.heatPhysical (4*(targets Zero k p i-(q:ℝ))) (centers Zero k p i) y‖)*
        MixedPastWordMoments.total (d:=1) P (fun j=>lower Zero k p j-(v:ℝ))
          (fun j=>upper Zero k p j-(v:ℝ)) (fun j=>targets Zero k p (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν=
        D0*ParentMeanDensity.globalDensity Zero k p q y := by
      simp only [D0,W,G,hglobal,htotal,hprod',
        sub_self,mul_zero,neg_zero,exp_zero,one_mul]
      ring
    simpa only [MixedPastLiteralPoint.point,Measure.restrict_univ,probReal_univ,mul_one,
      show 2*1=2 by norm_num,heq,a,m,C,one_mul] using hh
  have hh:=ControlledFamilyMeanFirstMoment.first_moment P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    μ a ha k m hm q p hqt (fun ω=>embed (S.second q ω-S.first q ω)) hV hVi D0 C hD0 hC hpoint
  dsimp only at hh
  have hgap : 0<(carrier Zero k).terminal p-(q:ℝ):=sub_pos.mpr hqt
  have hsqrt : sqrt (2*UniformFutureProfileScores.constant (1+k)/(P.lower*((carrier Zero k).terminal p-(q:ℝ))))=
      sqrt (2*UniformFutureProfileScores.constant (1+k)/P.lower)*((carrier Zero k).terminal p-(q:ℝ))^(-(1/2:ℝ)) := by
    rw [show 2*UniformFutureProfileScores.constant (1+k)/(P.lower*((carrier Zero k).terminal p-(q:ℝ)))=
      (2*UniformFutureProfileScores.constant (1+k)/P.lower)/((carrier Zero k).terminal p-(q:ℝ)) by field_simp]
    have hCf:=UniformFutureProfileScores.constant_pos (1+k)
    have hl:=P.lower_pos
    rw [Real.sqrt_div,show sqrt ((carrier Zero k).terminal p-(q:ℝ))=((carrier Zero k).terminal p-(q:ℝ))^(1/2:ℝ)
      from sqrt_eq_rpow _,div_eq_mul_inv,←rpow_neg hgap.le] <;> positivity
  have hac : StrictHistory Zero k p ∧ (q:ℝ)<(carrier Zero k).terminal p:=⟨hstrict,hqt⟩
  refine ⟨hh.1,?_⟩
  calc
    _≤_:=hh.2
    _=_:=by
      simp only [embed_norm,D0,hsqrt,PastMeanTimeFactors.absoluteDensity,PastMeanTimeFactors.totalIntegrand,
        ite_eq_left hac,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num,W,G]
      ring

end SHE.MixedPastMeanFirstMoment
