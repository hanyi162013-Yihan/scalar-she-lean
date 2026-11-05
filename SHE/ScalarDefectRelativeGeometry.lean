module

public import SHE.FixedHistoryTimeFactors
public import SHE.BoundedEmptyAssignmentTime
public import SHE.ScalarCarrierStops

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.ScalarDefectRelativeGeometry
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  StoppedGaussianScore
open scoped BigOperators
local instance scalarDefectRelativeGeometry_period:Fact (0<2*π):=⟨by positivity⟩
local instance scalarDefectRelativeGeometry_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {R:ReferenceData}{n:ℕ}(L:Level R HeatCircle n)(T:ℝ)(hT:∀x,L.terminal x=T)
variable (σ target:Fin n→ℝ)(a:Fin n→HeatCircle)
variable (hobs:∀x i,L.observations.observations x i=Observation.mk (σ i) (target i) (a i+x))
include T hT σ target a hobs

/-- Simultaneous root/old translation moves exactly every original
center and preserves every original stop and target. -/
theorem observations (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:HeatCircle):
    (carrier L k).observations.observations (separated k (x,t,fun i=>w i+x))=
      fun i=>let Z:=(carrier L k).observations.observations (separated k (0,t,w)) i
        Observation.mk Z.stop Z.target (Z.center+x):=by
  induction k with
  | zero=>
    funext i
    change L.observations.observations x i=
      Observation.mk (L.observations.observations 0 i).stop (L.observations.observations 0 i).target
        ((L.observations.observations 0 i).center+x)
    rw [hobs x i,hobs 0 i]
    simp only [add_zero]
  | succ k ih=>
    funext i
    refine Fin.cases ?_ (fun j=>congrFun (ih (fun i=>t i.succ) (fun i=>w i.succ)) j) i
    change Observation.mk ((carrier L k).nodeTime (separated (k+1) (x,t,fun i=>w i+x)))
        ((carrier L k).nodeTime (separated (k+1) (x,t,fun i=>w i+x))+0) (w 0+x)=
      Observation.mk ((carrier L k).nodeTime (separated (k+1) (0,t,w)))
        ((carrier L k).nodeTime (separated (k+1) (0,t,w))+0) (w 0+x)
    rw [FixedHistoryTimeFactors.nodeTime_separated L T hT,
      FixedHistoryTimeFactors.nodeTime_separated L T hT]

theorem unit_centers (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:AddCircle (1:ℝ)):
    (fun i=>(CircleNormalization.scale 1 (2*π)).symm
      (((carrier L k).observations.observations
        (separated k (CircleNormalization.scale 1 (2*π) x,t,
          fun j=>w j+CircleNormalization.scale 1 (2*π) x))) i).center)=
    (fun i=>(CircleNormalization.scale 1 (2*π)).symm
      (((carrier L k).observations.observations (separated k (0,t,w))) i).center+x):=by
  rw [observations L T hT σ target a hobs]
  funext i
  simp only [map_add,AddEquiv.symm_apply_apply]

omit T hT σ target a hobs

theorem leafScale_age (P:CanonicalCovariance.ProfileParameters){r m:ℕ}
    (cs:List (Fin r×Fin m))(l:Fin m)(lo hi:Fin r→ℝ)(age age':ℝ)
    (pick:GaussianAssignmentBlocks.block cs l≠[]→Fin r):
    BoundedEmptyAssignedLeaf.leafScale P cs l lo hi age pick=
      BoundedEmptyAssignedLeaf.leafScale P cs l lo hi age' pick:=by
  unfold BoundedEmptyAssignedLeaf.leafScale NativeAssignedLeafMoments.leafScale
  split_ifs <;>rfl

theorem total_age (P:CanonicalCovariance.ProfileParameters){r m d:ℕ}
    (lo hi:Fin r→ℝ)(age age':Fin m→ℝ)(A0 ν:ℝ):
    TwoFreshBoundedEmptyWord.total (d:=d) P lo hi age A0 ν=
      TwoFreshBoundedEmptyWord.total (d:=d) P lo hi age' A0 ν:=by
  unfold TwoFreshBoundedEmptyWord.total TwoFreshBoundedEmptyWord.factor
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs _
  apply congrArg abs
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact leafScale_age P cs j.succ lo hi (age j) (age' j) _

end SHE.ScalarDefectRelativeGeometry
