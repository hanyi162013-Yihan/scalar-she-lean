module

public import SHE.ScalarRootRelativeGeometry
public import SHE.SharpWordTimeScale
public import SHE.FixedHistoryDomain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ScalarRootRelativeGeometry
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  CoveredHistoryGeometry CoveredControlledLaw OrderedHeatForests ActualMeanKernel ControlledOldIntervals
  ControlledResidualScoreInput GaussianAssignmentBlocks
variable {R : ReferenceData} (L : Level R HeatCircle 1)
variable (T : ℝ) (hT : ∀ x,L.terminal x=T)

include T hT in
/-- The analytic small-history domain is common to all output roots
and relative insertion sites, with every original target retained. -/
theorem small_history_sections (A : ℝ)
    (hA : ∀ x i,(L.observations.observations x i).target=A)
    (Hs : ℕ→ℝ) (k : ℕ) (t : Fin k→ℝ) (x x' : HeatCircle) (z z' : Fin k→HeatCircle) :
    SmallHistory L Hs k (separated k (x,t,z)) ↔
      SmallHistory L Hs k (separated k (x',t,z')) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (SmallHistory L Hs k (separated k (x,(fun i=>t i.succ),(fun i=>z i.succ))) ∧
      ∀ i,targets L k (separated k (x,(fun i=>t i.succ),(fun i=>z i.succ))) i-
        (carrier L k).nodeTime (separated (k+1) (x,t,z))≤Hs k) ↔
      (SmallHistory L Hs k (separated k (x',(fun i=>t i.succ),(fun i=>z' i.succ))) ∧
      ∀ i,targets L k (separated k (x',(fun i=>t i.succ),(fun i=>z' i.succ))) i-
        (carrier L k).nodeTime (separated (k+1) (x',t,z'))≤Hs k)
    rw [ih,FixedHistoryTimeFactors.nodeTime_separated L T hT,
      FixedHistoryTimeFactors.nodeTime_separated L T hT,
      FixedHistoryTimeFactors.targets_sections L T hT (fun _=>A) hA]

include T hT in
/-- The complete sharp assignment sum, including each selected minimum
gap, is independent of the output root and old insertion sites. -/
theorem sharp_total_sections (P : CanonicalCovariance.ProfileParameters) (A : ℝ)
    (hA : ∀ x i,(L.observations.observations x i).target=A)
    (k : ℕ) (t : Fin k→ℝ) (x x' : HeatCircle) (z z' : Fin k→HeatCircle)
    (q A0 ν : ℝ) :
    SharpWordTimeScale.total L P k (separated k (x,t,z)) q A0 ν=
      SharpWordTimeScale.total L P k (separated k (x',t,z')) q A0 ν := by
  have hl := FixedHistoryTimeFactors.lower_sections L T hT k t x x' z z'
  have hu := FixedHistoryTimeFactors.upper_sections L T hT k t x x' z z'
  have ht := FixedHistoryTimeFactors.targets_sections L T hT (fun _=>A) hA k t x x' z z'
  have he : (carrier L k).terminal (separated k (x,t,z))=
      (carrier L k).terminal (separated k (x',t,z')) := by
    rw [terminal_separated L T hT,terminal_separated L T hT]
  have hc (cs : List (Fin k×Fin (k+1))) :
      SharpWordTimeScale.chosen L k (separated k (x,t,z)) q cs=
        SharpWordTimeScale.chosen L k (separated k (x',t,z')) q cs := by
    funext j h
    unfold SharpWordTimeScale.chosen
    simp only [lowerWith,upperWith,hl,hu,he]
  simp only [SharpWordTimeScale.total,SharpWordTimeScale.factor,hc,PhysicalWordTimeScale.factor,
    lowerWith,upperWith,hl,hu,ht,he]

include T hT in
/-- The original parent density in relative coordinates has the same
time array and the root fixed at zero. Orderedness proofs play no role
in this equality. -/
theorem parent_density_relative (κ : ℝ) (hκ : 0<κ) (A : ℝ)
    (hA : ∀ x i,(L.observations.observations x i).target=A)
    (hcenter : ∀ x i,(L.observations.observations x i).center=x)
    (k : ℕ) (t : Fin k→ℝ) (x : HeatCircle) (w : Fin k→HeatCircle)
    (ht : OrderedTimes k (targets L k (separated k (x,t,fun i=>w i+x)))) :
    parentDensity κ hκ k (targets L k (separated k (x,t,fun i=>w i+x))) ht
      (centers L k (separated k (x,t,fun i=>w i+x)))=
    parentDensity κ hκ k (targets L k (separated k ((0:HeatCircle),t,fun _=>0)))
      (by
        have htarget := FixedHistoryTimeFactors.targets_sections L T hT (fun _=>A) hA
          k t x 0 (fun i=>w i+x) (fun _=>0)
        simpa only [htarget] using ht)
      (values (fun _ : Fin 1=>(0:HeatCircle)) k w) := by
  have htarget := FixedHistoryTimeFactors.targets_sections L T hT (fun _=>A) hA
    k t x 0 (fun i=>w i+x) (fun _=>0)
  rw [centers_relative L hcenter]
  rw [parentDensity_translate]
  congr 1

end SHE.ScalarRootRelativeGeometry
