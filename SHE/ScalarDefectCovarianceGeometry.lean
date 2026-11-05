module

public import SHE.DefectRelativeFactor
public import SHE.NativeFirstScoreReserve
public import SHE.CarrierStopBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000

namespace SHE.ScalarDefectCovarianceGeometry
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw ControlledOldIntervals StoppedGaussianScore
local instance scalarDefectCovarianceGeometry_period:Fact (0<2*π):=⟨by positivity⟩
local instance scalarDefectCovarianceGeometry_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)(T:ℝ)(hT:∀x,L.terminal x=T)
variable (hroot:∀x i,(L.observations.observations x i).stop=T ∧
  (L.observations.observations x i).target=T ∧ (L.observations.observations x i).center=x)
include hT hroot

theorem covered_stop_eq_target (k:ℕ)(h:History HeatCircle k):stops L k h=targets L k h:=by
  funext i
  change min (((carrier L k).observations.observations h i).stop) (initialTerminal L k h)=_
  rw [min_eq_left (CarrierStopBounds.stop_le_initial L (fun x i=>by rw [(hroot x i).1,hT]) k h i)]
  exact ScalarCarrierStops.stop_eq_target L (fun x i=>(hroot x i).1.trans (hroot x i).2.1.symm) k h i

/-- Both fresh score laws retain their actual controlled profile,
under the simultaneous translation of ALL original root/old centers.
The profile itself is never translated or replaced by a constant law. -/
theorem covariances (P:CanonicalCovariance.ProfileParameters)(Λ v q θ:ℝ)(u d:CircleL2)
    (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:AddCircle (1:ℝ)):
    let h:=separated k (CircleNormalization.scale 1 (2*π) x,t,
      fun i=>w i+CircleNormalization.scale 1 (2*π) x)
    let z:=separated k ((0:HeatCircle),t,fun _=>0)
    let a:=fun i=>(CircleNormalization.scale 1 (2*π)).symm
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
    let σ:=fun i=>stops L k z i-v
    let target:=fun i=>targets L k z i-v
    let lo:=fun j=>lower L k z j-v
    let hi:=fun j=>upper L k z j-v
    NativeFirstScoreReserve.covariance P (fun i=>stops L k h i-v)
      (fun i=>targets L k h i-v) (centers L k h) (q-v)=
        NativeFirstScoreReserve.covariance P σ target (nativeCenter (fun i=>a i+x)) (q-v) ∧
    ControlledFixedReserve.covariance P Λ u d
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d
        (fun j=>lower L k h j-v) (fun j=>upper L k h j-v)))
      (fun i=>stops L k h i-v) (fun i=>targets L k h i-v) (centers L k h) (q-v) θ=
        ControlledFixedReserve.covariance P Λ u d
          (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d lo hi))
          σ target (nativeCenter (fun i=>a i+x)) (q-v) θ:=by
  intro h z a σ target lo hi
  have hs:=ScalarRootRelativeGeometry.covered_stops_sections L T hT T
    (fun x i=>(hroot x i).1) k t (CircleNormalization.scale 1 (2*π) x) 0
      (fun i=>w i+CircleNormalization.scale 1 (2*π) x) (fun _=>0)
  have ht:=FixedHistoryTimeFactors.targets_sections L T hT (fun _=>T)
    (fun x i=>(hroot x i).2.1) k t (CircleNormalization.scale 1 (2*π) x) 0
      (fun i=>w i+CircleNormalization.scale 1 (2*π) x) (fun _=>0)
  have hc:centers L k h=nativeCenter (fun i=>a i+x):=by
    rw [ScalarRootRelativeGeometry.centers_relative L (fun x i=>(hroot x i).2.2)]
    funext i
    change OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i+
      CircleNormalization.scale 1 (2*π) x=CircleNormalization.scale 1 (2*π) (a i+x)
    rw [map_add,AddEquiv.apply_symm_apply]
  rw [hs,ht,hc,
    FixedHistoryTimeFactors.lower_sections L T hT k t (CircleNormalization.scale 1 (2*π) x) 0
      (fun i=>w i+CircleNormalization.scale 1 (2*π) x) (fun _=>0),
    FixedHistoryTimeFactors.upper_sections L T hT k t (CircleNormalization.scale 1 (2*π) x) 0
      (fun i=>w i+CircleNormalization.scale 1 (2*π) x) (fun _=>0)]
  exact ⟨rfl,rfl⟩

end SHE.ScalarDefectCovarianceGeometry
