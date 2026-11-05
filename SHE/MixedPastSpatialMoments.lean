module

public import SHE.MixedPastLiteralFields
public import SHE.ControlledFamilyHistoryMoments
public import SHE.PastMeanAmplitude

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

namespace SHE.MixedPastSpatialMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastSpatialMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastSpatialMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastSpatialMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastSpatialMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastSpatialMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastSpatialMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastSpatialMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastSpatialMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastSpatialMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- The actual mixed random-past weighted mean kernel, after averaging
every old spatial location. The q-law and true joint current mean are
unchanged, the quarter row is chosen before Fubini, and all Gaussian,
conditional, geometric and moment applicability inputs are proved. The
remaining displayed conditions are only fixed dimensional local spans
and the actual root jets. -/
theorem quarter_spatial_even_moment (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target≤(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (root : Measure X) [IsFiniteMeasure root] (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (θ : ℝ) (hθ : |θ|≤1) (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order : ℕ) (horder : 0<order) (B0 : ℝ≥0)
    (hBDG : StandardTerminalBDGPower (order*(k+2)) J B0)
    (q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) :
    let C:=MixedPastWordMoments.momentConstant P k k order
      ((k:ℝ)*(NativeHybridMoments.momentConstant (order*(k+2)) B0 κ M)^P.exponent)
    ∀ᵐ x ∂root,∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let p0:=separated k (x,t,fun _=>(0:HeatCircle))
      ∀ hp : StrictHistory Zero k p0,(q:ℝ)<(carrier Zero k).terminal p0 →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        let r:=HistoryQuarterFields.rowTime Zero k (q:ℝ) p0
        Integrable (fun ω=>‖weightedSpatial (Base (θ,(U ω,Dir ω))) k Λ q r
          (fun _ : Unit=>Mean k θ q ω) t () y x‖^(2*order)) μ ∧
          (∫ ω,‖weightedSpatial (Base (θ,(U ω,Dir ω))) k Λ q r
            (fun _ : Unit=>Mean k θ q ω) t () y x‖^(2*order) ∂μ)≤
            C*(PastMeanAmplitude.damped Zero P k Λ q A0 ν p0*
              ScalarMeanEnvelope.massBudget Zero k p0 1 r y)^(2*order) := by
  intro C
  let a : Ω→ℝ×Inputs:=fun ω=>(θ,(U ω,Dir ω))
  let r:=HistoryQuarterFields.rowTime Zero k (q:ℝ)
  let D:=PastMeanAmplitude.damped Zero P k Λ (q:ℝ) A0 ν
  let m:=Mean k θ q
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hDir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have ha : Measurable a:=measurable_const.prodMk (hU.prodMk hDir)
  have hm : Measurable (fun z : Ω×History X k=>m z.1 z.2):=
    MixedPastLiteralFields.meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q
  have hC : 0≤C:=MixedPastWordMoments.momentConstant_nonneg P k k order _
  have hpall:=MixedPastLiteralPoint.conditional_even_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
    hlocal hΛ hages hrootStop hspan root k
  have hp : ∀ᵐ p ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) root k,
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        True ∧ StrictHistory Zero k p ∧ r p<(carrier Zero k).terminal p →
        (∫ ω,|weightedPoint (Base (a ω)) k Λ q (r p) (m ω) p y|^(2*order) ∂μ)≤
          C*(D p*ParentMeanDensity.globalDensity Zero k p (r p) y)^(2*order) := by
    filter_upwards [hpall] with p hp
    by_cases hgood : StrictHistory Zero k p ∧ r p<(carrier Zero k).terminal p
    · have hqp : (q:ℝ)<(carrier Zero k).terminal p :=
        (HistoryQuarterFields.le_rowTime Zero k (q:ℝ) p).trans_lt hgood.2
      have hsmall : SmallHistory Zero (uniformHorizon 1) k p :=
        RelativeHistoryGeometry.smallHistory_of_span Zero (b:ℝ) (fun _=>le_rfl) hrootTarget
          (uniformHorizon 1) k hold p
      have hsmallf (i) : targets Zero k p i-r p≤UniformFutureProfileScores.horizon (1+k) :=
        (RelativeHistoryGeometry.carrier_age_le_span Zero (b:ℝ) (fun _=>le_rfl) hrootTarget k p
          (by exact (show (v:ℝ)≤(q:ℝ) from by exact_mod_cast hvq).trans (HistoryQuarterFields.le_rowTime Zero k (q:ℝ) p)) i).trans hfresh
      have he:=hp q hvq hqH hqp (r p) (HistoryQuarterFields.le_rowTime Zero k (q:ℝ) p) hgood.2
        hsmallf hgood.1 hsmall θ hθ A0 ν hA0 hν (hjet (rootParameter k p)) order horder B0 hBDG
      filter_upwards [he] with y hy
      intro _
      have hbound:=(hy univ MeasurableSet.univ).2
      have hW : 0≤timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k p :=
        timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
          (fun j=>(uniformConstant_pos 1 j).le) k p hgood.1
      have hprod:=ParentMeanDensity.parentProduct_eq_parentDensity Zero hages k p hgood.1
      have hprod' : ParentMeanDensity.parentProduct Zero k p=
          OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k p)
            (carrier_orderedTimes Zero hages k p hgood.1) (centers Zero k p) := hprod
      have htotal : PastWordTimeFields.total Zero P k p A0 ν=
          MixedPastWordMoments.total (d:=1) P (fun j=>lower Zero k p j-(v:ℝ))
            (fun j=>upper Zero k p j-(v:ℝ))
            (fun j=>targets Zero k p (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν := rfl
      have heq :
          (timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k p*
            OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k p)
              (carrier_orderedTimes Zero hages k p hgood.1) (centers Zero k p))*
          (exp (-Λ*(r p-(q:ℝ)))*sqrt (2*UniformFutureProfileScores.constant (1+k)/
            (P.lower*((carrier Zero k).terminal p-r p)))*
              ∑ i,Real.sqrt ‖ProfileVariance.heatPhysical (4*(targets Zero k p i-r p)) (centers Zero k p i) y‖)*
          MixedPastWordMoments.total (d:=1) P (fun j=>lower Zero k p j-(v:ℝ))
            (fun j=>upper Zero k p j-(v:ℝ)) (fun j=>targets Zero k p (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν=
          D p*ParentMeanDensity.globalDensity Zero k p (r p) y := by
        simp only [D,PastMeanAmplitude.damped,PastMeanAmplitude.value,max_eq_left hW,
          ParentMeanDensity.globalDensity,htotal,hprod',targets,centers]
        ring
      rw [heq] at hbound
      simpa only [MixedPastLiteralPoint.point,Measure.restrict_univ,probReal_univ,mul_one,C,a,m] using hbound
    · exact ae_of_all _ (fun _ h=>False.elim (hgood ⟨h.2.1,h.2.2⟩))
  have hh:=ControlledFamilyHistoryMoments.spatial_history_moment P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm μ hΛ hages root
    a ha k m hm q r D (HistoryQuarterFields.rowTime_measurable Zero k q)
      (PastMeanAmplitude.damped_measurable Zero P k Λ q A0 ν)
      (PastMeanAmplitude.damped_nonneg Zero P k Λ q A0 ν)
      (HistoryQuarterFields.rowTime_replaceSpace Zero k q)
      (PastMeanAmplitude.damped_replaceSpace Zero P k Λ q A0 ν)
      (fun _=>True) MeasurableSet.univ (fun _ _=>Iff.rfl) C hC order horder hp
  filter_upwards [hh] with x hx
  filter_upwards [hx] with t ht
  intro p0 hstrict hq
  exact ht trivial hstrict ((HistoryQuarterFields.rowTime_lt_iff Zero k q p0).mpr hq)

end SHE.MixedPastSpatialMoments
