module

public import SHE.MixedJointUncutDefectTrace
public import SHE.ScalarDefectRelativeHaar
public import SHE.MixedJointUncutMark
public import SHE.NativeDefectHaarAction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedScalarRelativeDefectTrace
open Set MeasureTheory Real StoppedFourier OrthogonalItoChannels FiniteHaar PredictableL2 NativeHeatObservation
  DyadicApproximation
  CutoffWordLevel CutoffWordHistories CutoffCarriers UncutWordEvaluation GaussianItoTest
  GaussianTaylorAverage JointWordAnalytic
open scoped NNReal
local instance mixedJointUncutDefectTrace_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedJointUncutDefectTrace_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedJointUncutDefectTrace_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedJointUncutDefectTrace_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R:ReferenceData}(L:Level R HeatCircle 1)
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U"=>(dU).physicalState
local notation "V"=>(dV).physicalState
local notation "XU"=>(dU).physicalField
local notation "XV"=>(dV).physicalField


open AddCircle HistoryProductMeasure CoveredControlledLaw StoppedGaussianScore
variable (T:ℝ)(hT:∀x,L.terminal x=T)
variable (hroot:∀x i,(L.observations.observations x i).stop=T ∧
  (L.observations.observations x i).target=T ∧ (L.observations.observations x i).center=x)

include hT hroot in
/-- Exact actual full first-defect point in relative old-space and
clock coordinates, with the SAME current fields, actual covariance,
actual joint mean, and ALL THREE original matched Haar contractions. -/
theorem point_trace (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:AddCircle (1:ℝ))
    (v q:ℝ)(hq:0≤q)(ω:Ω):
    let h:=separated k (CircleNormalization.scale 1 (2*π) x,t,
      fun i=>w i+CircleNormalization.scale 1 (2*π) x)
    let z:=separated k ((0:HeatCircle),t,fun _=>0)
    let a:=fun i=>(CircleNormalization.scale 1 (2*π)).symm
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
    let c:=ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q.toNNReal,ω)
    let d:=ContinuousHeatMild.coefficientFunction haV hell hbV S.second (q.toNNReal,ω)
    let B:=GaussianTaylor.hessian (GaussianConvolution.gaussianAverage
      (WordRecursion.covariance R.reference ((carrier L k).observations.observations h)
        q ((carrier L k).terminal h)) (UncutSmoothWords.test L k h))
          (state (carrier L k) Λ U V XU XV h ω q)
    let D:=NativeClippedHaarDirection.column hell c d
      (fun i=>stops L k z i-v) (fun i=>targets L k z i-v) (fun i=>a i+x) (q-v) Λ
    let W:=CommonHaarDefectTrace.direction
      (fun i=>NativeObservationCovariance.row hell d (targets L k z i-v) (q-v)
        (nativeCenter (fun i=>a i+x) i))
    Summable (fun l:HaarNode=>B (D l) (W l)+B (W l) (D l)+B (D l) (D l)) ∧
      MixedJointUncutDefectTrace.point
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k h ω q=
          (1/2:ℝ)*(∑'l:HaarNode,(B (D l) (W l)+B (W l) (D l)+B (D l) (D l))):=by
  intro h z a c d B D W
  let Z:=(carrier L k).observations.observations h
  let ah:=fun i=>(CircleNormalization.scale 1 (2*π)).symm (Z i).center
  let D0:=NativeClippedHaarDirection.column hell c d (fun i=>(Z i).stop)
    (fun i=>(Z i).target) ah q Λ
  let W0:=CommonHaarDefectTrace.direction
    (fun i=>NativeObservationCovariance.row hell d (Z i).target q (Z i).center)
  have hσ:stops L k h=fun i=>(Z i).stop:=by
    funext i
    exact min_eq_left (CarrierStopBounds.stop_le_initial L
      (fun y j=>by rw [(hroot y j).1,hT]) k h i)
  have hD:D=D0:=by
    funext l
    calc
      D l=NativeClippedHaarDirection.column hell c d
          (fun i=>stops L k h i-v) (fun i=>targets L k h i-v)
          (fun i=>(CircleNormalization.scale 1 (2*π)).symm (centers L k h i)) (q-v) Λ l:=
        (ScalarDefectRelativeHaar.clipped L T hT hroot hell c d k t w x v q Λ l).symm
      _=NativeClippedHaarDirection.column hell c d (stops L k h) (targets L k h)
          (fun i=>(CircleNormalization.scale 1 (2*π)).symm (centers L k h i)) q Λ l:=
        NativeHaarTimeTranslation.clipped hell c d _ _ _ q v Λ l
      _=D0 l:=by rw [hσ];rfl
  have hW:W=W0:=by
    funext l
    calc
      W l=CommonHaarDefectTrace.direction
          (fun i=>NativeObservationCovariance.row hell d (targets L k h i-v) (q-v) (centers L k h i)) l:=
        (ScalarDefectRelativeHaar.current L T hT hroot hell d k t w x v q l).symm
      _=CommonHaarDefectTrace.direction
          (fun i=>NativeObservationCovariance.row hell d (targets L k h i) q (centers L k h i)) l:=
        NativeHaarTimeTranslation.current hell d _ _ q v l
      _=W0 l:=rfl
  have hh:=MixedJointUncutDefectTrace.point_trace
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k h ω q hq
  change Summable (fun l:HaarNode=>B (D0 l) (W0 l)+B (W0 l) (D0 l)+B (D0 l) (D0 l)) ∧
    MixedJointUncutDefectTrace.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k h ω q=
      (1/2:ℝ)*(∑'l:HaarNode,(B (D0 l) (W0 l)+B (W0 l) (D0 l)+B (D0 l) (D0 l))) at hh
  rw [hD,hW]
  exact hh

end SHE.MixedScalarRelativeDefectTrace
