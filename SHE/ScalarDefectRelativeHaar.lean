module

public import SHE.ScalarDefectCovarianceGeometry
public import SHE.NativeHaarTimeTranslation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace SHE.ScalarDefectRelativeHaar
open Set MeasureTheory Real AddCircle FiniteHaar StoppedFourier StoppedGaussianScore
  StoppedGaussianFeatures GaussianIncrement MeasurableGaussianScores CommonHaarDefectTrace
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays
  PhysicalParentGeometry PhysicalScoreChain CoveredControlledLaw ControlledProfile ControlledOldIntervals
  HistoryProductMeasure
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)(T:ℝ)(hT:∀x,L.terminal x=T)
variable (hroot:∀x i,(L.observations.observations x i).stop=T ∧
  (L.observations.observations x i).target=T ∧ (L.observations.observations x i).center=x)

include hT hroot in
theorem center_eq (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:AddCircle (1:ℝ)):
    let h:=separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
      fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x)
    let a:=fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
    centers L k h=nativeCenter (fun i=>a i+x):=by
  intro h a
  rw [ScalarRootRelativeGeometry.centers_relative L (fun x i=>(hroot x i).2.2)]
  funext i
  change OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i+
    CircleNormalization.scale 1 (2*Real.pi) x=CircleNormalization.scale 1 (2*Real.pi) (a i+x)
  rw [map_add,AddEquiv.apply_symm_apply]

include hT hroot in
theorem clipped {m W:ℝ}(hm:0<m)(f g:EllipticField m W)
    (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:AddCircle (1:ℝ))(v q Λ:ℝ)(l:HaarNode):
    let h:=separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
      fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x)
    let z:=separated k ((0:HeatCircle),t,fun _=>0)
    let a:=fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
    NativeClippedHaarDirection.column hm f g (fun i=>stops L k h i-v) (fun i=>targets L k h i-v)
      (fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm (centers L k h i)) (q-v) Λ l=
      NativeClippedHaarDirection.column hm f g (fun i=>stops L k z i-v) (fun i=>targets L k z i-v)
        (fun i=>a i+x) (q-v) Λ l:=by
  intro h z a
  have hs:=ScalarRootRelativeGeometry.covered_stops_sections L T hT T (fun x i=>(hroot x i).1)
    k t (CircleNormalization.scale 1 (2*Real.pi) x) 0
      (fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x) (fun _=>0)
  have ht:=FixedHistoryTimeFactors.targets_sections L T hT (fun _=>T) (fun x i=>(hroot x i).2.1)
    k t (CircleNormalization.scale 1 (2*Real.pi) x) 0
      (fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x) (fun _=>0)
  have hc:=center_eq L T hT hroot k t w x
  apply PiLp.ext
  intro i
  change (1-exp (-Λ*((stops L k h i-v)-(q-v))))*
    (NativeObservationCovariance.row hm f (targets L k h i-v) (q-v)
        (CircleNormalization.scale 1 (2*Real.pi) ((CircleNormalization.scale 1 (2*Real.pi)).symm (centers L k h i))) l-
      NativeObservationCovariance.row hm g (targets L k h i-v) (q-v)
        (CircleNormalization.scale 1 (2*Real.pi) ((CircleNormalization.scale 1 (2*Real.pi)).symm (centers L k h i))) l)=_
  rw [AddEquiv.apply_symm_apply,congrFun hs i,congrFun ht i,congrFun hc i]
  rfl

include hT hroot in
theorem current {m W:ℝ}(hm:0<m)(g:EllipticField m W)
    (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:AddCircle (1:ℝ))(v q:ℝ)(l:HaarNode):
    let h:=separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
      fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x)
    let z:=separated k ((0:HeatCircle),t,fun _=>0)
    let a:=fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
    direction (fun i=>NativeObservationCovariance.row hm g (targets L k h i-v) (q-v) (centers L k h i)) l=
      direction (fun i=>NativeObservationCovariance.row hm g (targets L k z i-v) (q-v)
        (nativeCenter (fun i=>a i+x) i)) l:=by
  intro h z a
  have ht:=FixedHistoryTimeFactors.targets_sections L T hT (fun _=>T) (fun x i=>(hroot x i).2.1)
    k t (CircleNormalization.scale 1 (2*Real.pi) x) 0
      (fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x) (fun _=>0)
  rw [ht,center_eq L T hT hroot k t w x]

end SHE.ScalarDefectRelativeHaar
