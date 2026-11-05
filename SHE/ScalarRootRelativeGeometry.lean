module

public import SHE.FixedHistoryTimeFactors
public import SHE.ForestTranslation
public import SHE.ControlledFullResidualInput
public import SHE.ParentHeatFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ScalarRootRelativeGeometry
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  CoveredHistoryGeometry CoveredControlledLaw OrderedHeatForests ActualMeanKernel ControlledOldIntervals
  ControlledResidualScoreInput
open scoped BigOperators
local instance scalarRootRelativeGeometry_periodPos : Fact (0<2*π) := ⟨by positivity⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)
variable (T : ℝ) (hT : ∀ x,L.terminal x=T)

include T hT in
theorem original_stops_sections (σ : ℝ)
    (hσ : ∀ x i,(L.observations.observations x i).stop=σ)
    (k : ℕ) (t : Fin k→ℝ) (x x' : HeatCircle) (z z' : Fin k→HeatCircle) :
    (fun i=>((carrier L k).observations.observations (separated k (x,t,z)) i).stop)=
      fun i=>((carrier L k).observations.observations (separated k (x',t,z')) i).stop := by
  induction k with
  | zero => funext i;exact (hσ x i).trans (hσ x' i).symm
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j=>congrFun (ih (fun i=>t i.succ) (fun i=>z i.succ) (fun i=>z' i.succ)) j) i
    change (carrier L k).nodeTime (separated (k+1) (x,t,z))=
      (carrier L k).nodeTime (separated (k+1) (x',t,z'))
    rw [FixedHistoryTimeFactors.nodeTime_separated L T hT,FixedHistoryTimeFactors.nodeTime_separated L T hT]

include T hT in
theorem covered_stops_sections (σ : ℝ)
    (hσ : ∀ x i,(L.observations.observations x i).stop=σ)
    (k : ℕ) (t : Fin k→ℝ) (x x' : HeatCircle) (z z' : Fin k→HeatCircle) :
    stops L k (separated k (x,t,z))=stops L k (separated k (x',t,z')) := by
  have hs := original_stops_sections L T hT σ hσ k t x x' z z'
  funext i
  change min (((carrier L k).observations.observations (separated k (x,t,z)) i).stop)
      (L.terminal (rootParameter k (separated k (x,t,z))))=
    min (((carrier L k).observations.observations (separated k (x',t,z')) i).stop)
      (L.terminal (rootParameter k (separated k (x',t,z'))))
  rw [root_separated,root_separated,hT,hT,congrFun hs i]

theorem centers_sections (hcenter : ∀ x i,(L.observations.observations x i).center=x)
    (k : ℕ) (t : Fin k→ℝ) (x : HeatCircle) (z : Fin k→HeatCircle) :
    centers L k (separated k (x,t,z))=values (fun _ : Fin 1=>x) k z := by
  have hh := replaceSpace_centers L k (separated k (x,t,fun _=>(0:HeatCircle))) z
  rw [replaceSpace_separated] at hh
  change (fun i=>((carrier L k).observations.observations (separated k (x,t,z)) i).center)=_
  simpa only [root_separated,hcenter] using hh

theorem centers_relative (hcenter : ∀ x i,(L.observations.observations x i).center=x)
    (k : ℕ) (t : Fin k→ℝ) (x : HeatCircle) (w : Fin k→HeatCircle) :
    centers L k (separated k (x,t,fun i=>w i+x))=
      fun i=>values (fun _ : Fin 1=>(0:HeatCircle)) k w i+x := by
  rw [centers_sections L hcenter]
  simpa only [zero_add] using values_translate (fun _ : Fin 1=>(0:HeatCircle)) k w x

theorem parentDensity_translate (κ : ℝ) (hκ : 0<κ) (k : ℕ)
    (t : Fin (1+k)→ℝ) (ht : OrderedTimes k t) (z : Fin (1+k)→HeatCircle) (x : HeatCircle) :
    parentDensity κ hκ k t ht (fun i=>z i+x)=parentDensity κ hκ k t ht z := by
  simp_rw [←sum_density_eq κ hκ k t ht,density_translate]

include T hT in
/-- The actual full future-input field on original history coordinates
is exactly its relative-space field. Fixed old fractions depend only on
the unchanged original time arrays, even though the profile is spatially
inhomogeneous. -/
theorem future_input_relative (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (θ : ℝ) (σ A : ℝ)
    (hσ : ∀ x i,(L.observations.observations x i).stop=σ)
    (hA : ∀ x i,(L.observations.observations x i).target=A)
    (hcenter : ∀ x i,(L.observations.observations x i).center=x)
    (k : ℕ) (t : Fin k→ℝ) (x : HeatCircle) (w : Fin k→HeatCircle)
    (e : StoppedGaussianFeatures.Domain→ℝ) (q : ℝ) :
    let p := separated k (x,t,fun i=>w i+x)
    let a := separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
    futureInput (stops L k p) (targets L k p) (centers L k p)
      (fun r=>ControlledProfile.profile P Λ u d (θ,r)-fixedProfile P Λ u d (lower L k p) (upper L k p) r) e q 0=
    futureInput (stops L k a) (targets L k a) (values (fun _ : Fin 1=>(0:HeatCircle)) k w)
      (fun r=>ControlledProfile.profile P Λ u d (θ,r)-fixedProfile P Λ u d (lower L k a) (upper L k a) r) e q x := by
  dsimp only
  rw [covered_stops_sections L T hT σ hσ k t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.targets_sections L T hT (fun _=>A) hA k t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.lower_sections L T hT k t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.upper_sections L T hT k t x 0 _ (fun _=>0),
    centers_relative L hcenter]
  simp only [futureInput,add_zero]

end SHE.ScalarRootRelativeGeometry
