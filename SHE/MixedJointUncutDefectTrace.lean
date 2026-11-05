module

public import SHE.MixedJointUncutMark
public import SHE.NativeDefectHaarAction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedJointUncutDefectTrace
open Set MeasureTheory Real StoppedFourier OrthogonalItoChannels FiniteHaar PredictableL2 NativeHeatObservation
  DyadicApproximation
  CutoffWordLevel CutoffWordHistories CutoffCarriers UncutWordEvaluation GaussianItoTest
  GaussianTaylorAverage JointWordAnalytic
open scoped NNReal
local instance mixedJointUncutDefectTrace_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedJointUncutDefectTrace_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedJointUncutDefectTrace_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedJointUncutDefectTrace_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω X:Type}[MeasurableSpace Ω][MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R:ReferenceData}{n:ℕ}(L:Level R X n)
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U"=>(dU).physicalState
local notation "V"=>(dV).physicalState
local notation "XU"=>(dU).physicalField
local notation "XV"=>(dV).physicalField

def point (k:ℕ)(h:History X k)(ω:Ω)(q:ℝ):ℝ:=
  (1/2:ℝ)*covarianceAction
    (MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (normalizedLevel L k) ((h,ω),q))
    (GaussianTaylor.hessian (GaussianConvolution.gaussianAverage
      (WordRecursion.covariance R.reference ((carrier L k).observations.observations h)
        q ((carrier L k).terminal h)) (UncutSmoothWords.test L k h))
      (state (carrier L k) Λ U V XU XV h ω q))
local notation "Pt"=>point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem point_eq_weight (k:ℕ)(h:History X k)(ω:Ω)(q:ℝ)
    (hq:q∈Icc R.base ((carrier L k).terminal h)):
    Pt k h ω q=UncutSmoothWords.weight L k h*
      JointWordDefect.integrand (normalizedLevel L k) Λ U V XU XV
        (MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (normalizedLevel L k)) ((h,ω),q):=by
  have hb:GaussianConvolution.gaussianAverage
      (WordRecursion.covariance R.reference ((carrier L k).observations.observations h)
        q ((carrier L k).terminal h)) (UncutSmoothWords.test L k h)=
      UncutSmoothWords.weight L k h • backward ((normalizedLevel L k).window h)
        ((normalizedLevel L k).test h) q:=by
    rw [UncutSmoothWords.test_eq_weight_normalized,backward,
      ((normalizedLevel L k).window h).path_eq hq]
    change GaussianSmooth.average _ (_ • _)=_ • GaussianSmooth.average _ _
    rw [NormalizedInsertion.average_smul]
    rfl
  rw [point,hb,NormalizedInsertion.hessian_smul]
  simp only [Pi.smul_apply,JointDefectScaling.action_smul]
  unfold JointWordDefect.integrand JointWordHessian.field
  dsimp only [JointWordAnalytic.state,normalizedLevel]
  ring

/-- The literal first-defect mark is exactly the current-time integral
of the full original uncut Gaussian-front Hessian. The original old
normalization is included, rather than added as an applicability premise. -/
theorem mark_eq_integral (k:ℕ)(h:History X k)(ω:Ω):
    MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k h ω=
      ∫q in R.base..(carrier L k).terminal h,Pt k h ω q:=by
  unfold MixedJointUncutMark.mark MixedJointLevelData.mark JointWordDefect.mark
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro q hq
  change q∈uIcc R.base ((carrier L k).terminal h) at hq
  rw [uIcc_of_le ((carrier L k).terminal_base h)] at hq
  exact (point_eq_weight 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k h ω q hq).symm

def activePoint (k:ℕ)(z:(History X k×Ω)×ℝ):ℝ:=
  if R.base≤z.2 ∧ z.2≤(carrier L k).terminal z.1.1 then Pt k z.1.1 z.1.2 z.2 else 0

/-- Genuine joint history/sample/current-time Borel field of the
original full first-defect point. The closed endpoints are immaterial
to its time integral and make the interval identity exact pointwise. -/
theorem activePoint_measurable (k:ℕ):Measurable
    (activePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k):=by
  classical
  have hI:=JointWordDefect.integrand_measurable (normalizedLevel L k) Λ
    (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable
    (MixedJointLevelData.defect_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (normalizedLevel L k))
  have hs:MeasurableSet {z:(History X k×Ω)×ℝ|R.base≤z.2 ∧ z.2≤(carrier L k).terminal z.1.1}:=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd ((carrier L k).terminal_measurable.comp measurable_fst.fst))
  have hm:Measurable (fun z:(History X k×Ω)×ℝ=>
      if R.base≤z.2 ∧ z.2≤(carrier L k).terminal z.1.1 then
        UncutSmoothWords.weight L k z.1.1*JointWordDefect.integrand (normalizedLevel L k)
          Λ U V XU XV (MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
            I₀ I₁ u₀ v₀ S (normalizedLevel L k)) z else (0:ℝ)):=
    (((UncutSmoothWords.weight_measurable L k).comp measurable_fst.fst).mul hI).ite hs measurable_const
  convert! hm using 1
  funext z
  by_cases hz:R.base≤z.2 ∧ z.2≤(carrier L k).terminal z.1.1
  · simp only [activePoint,if_pos hz]
    exact point_eq_weight 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k z.1.1 z.1.2 z.2 hz
  · simp only [activePoint,if_neg hz]

theorem mark_eq_active_integral (k:ℕ)(h:History X k)(ω:Ω):
    MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k h ω=
      ∫q in R.base..(carrier L k).terminal h,
        activePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k ((h,ω),q):=by
  rw [mark_eq_integral]
  apply intervalIntegral.integral_congr
  intro q hq
  rw [uIcc_of_le ((carrier L k).terminal_base h)] at hq
  change Pt k h ω q=if R.base≤q ∧ q≤(carrier L k).terminal h then Pt k h ω q else 0
  exact (if_pos ⟨hq.1,hq.2⟩).symm

/-- The actual mixed uncut first-defect point is the sum of its TWO
cross terms and its quadratic term along the ORIGINAL matched Haar
coordinates. This is an equality with the physical pair, not an
independently supplied covariance mark. -/
theorem point_trace (k:ℕ)(h:History X k)(ω:Ω)(q:ℝ)(hq:0≤q):
    let Z:=(carrier L k).observations.observations h
    let a:=fun i=>(CircleNormalization.scale 1 (2*π)).symm (Z i).center
    let c:=ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q.toNNReal,ω)
    let d:=ContinuousHeatMild.coefficientFunction haV hell hbV S.second (q.toNNReal,ω)
    let B:=GaussianTaylor.hessian (GaussianConvolution.gaussianAverage
      (WordRecursion.covariance R.reference Z q ((carrier L k).terminal h))
      (UncutSmoothWords.test L k h)) (state (carrier L k) Λ U V XU XV h ω q)
    let D:=fun l:HaarNode=>NativeClippedHaarDirection.column hell c d
      (fun i=>(Z i).stop) (fun i=>(Z i).target) a q Λ l
    let W:=fun l:HaarNode=>CommonHaarDefectTrace.direction
      (fun i=>NativeObservationCovariance.row hell d (Z i).target q (Z i).center) l
    Summable (fun l:HaarNode=>B (D l) (W l)+B (W l) (D l)+B (D l) (D l)) ∧
      Pt k h ω q=(1/2:ℝ)*(∑'l:HaarNode,(B (D l) (W l)+B (W l) (D l)+B (D l) (D l))):=by
  intro Z a c d B D W
  have ha:StoppedGaussianScore.nativeCenter a=fun i=>(Z i).center:=by
    funext i
    exact (CircleNormalization.scale 1 (2*π)).apply_symm_apply _
  have hai(i:Fin (n+k)):StoppedGaussianScore.nativeCenter a i=(Z i).center:=congrFun ha i
  have hh:=NativeDefectHaarAction.action_trace hell c d
    (fun i=>(Z i).stop) (fun i=>(Z i).target) a q Λ B
  simp_rw [hai] at hh
  rw [ha] at hh
  refine ⟨hh.1,?_⟩
  change (1/2:ℝ)*covarianceAction
    (MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (normalizedLevel L k) ((h,ω),q)) B=_
  rw [MixedJointLevelData.defect,MixedJointDefectFields.defect_eq_matrix,
    Real.coe_toNNReal q hq]
  change (1/2:ℝ)*covarianceAction
    (JointNativeDefect.matrix hell Λ (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>(Z i).center) c d q) B=_
  exact congrArg (fun z:ℝ=>(1/2:ℝ)*z) hh.2

end SHE.MixedJointUncutDefectTrace
