module

public import SHE.BaselineAssignmentScale
public import SHE.SharpTimeSections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.OmittedTimeFactor
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays CoveredHistoryGeometry CoveredControlledLaw
  GaussianCoordinates GaussianAssignmentBlocks PhysicalParentGeometry HistoryProductMeasure
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

theorem chosen_replaceSpace (k : ℕ) (p : History X k) (cs : List (Fin k×Fin (k+1)))
    (x : Fin k→HeatCircle) :
    OldOnlyTimeFactor.chosen L k (replaceSpace k p x) cs=OldOnlyTimeFactor.chosen L k p cs := by
  funext j h
  simp only [OldOnlyTimeFactor.chosen,PhysicalWordTimeScale.lower_replaceSpace,
    PhysicalWordTimeScale.upper_replaceSpace]

theorem factor_replaceSpace (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (cs : List (Fin k×Fin (k+1))) (j0 : Fin k) (A0 ν : ℝ) (x : Fin k→HeatCircle) :
    factor L P k (replaceSpace k p x) cs j0 A0 ν=factor L P k p cs j0 A0 ν := by
  have ht : targets L k (replaceSpace k p x)=targets L k p := replaceSpace_targets L k p x
  simp only [factor,chosen_replaceSpace,PhysicalWordTimeScale.lower_replaceSpace,
    PhysicalWordTimeScale.upper_replaceSpace,ht]

theorem factor_measurable (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (cs : List (Fin k×Fin (k+1))) (j0 : Fin k) (A0 ν : ℝ) :
    Measurable (fun p : History X k=>factor L P k p cs j0 A0 ν) := by
  have hroot : Measurable (fun p : History X k=>
      VectorPhysicalRoot.scale cs 0 (lower L k p) (upper L k p) A0 ν (P.lower/2) n) := by
    unfold VectorPhysicalRoot.scale
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.min (((upper_measurable L k _).sub
      (lower_measurable L k _)).pow_const (1/4:ℝ) |>.const_mul _)
  refine hroot.mul (Finset.measurable_prod (Finset.univ.erase j0) (fun j _=>?_))
  unfold NativeAssignedLeafMoments.leafScale
  split_ifs with h
  · exact measurable_const.mul
      (((carrier L k).observations.target_measurable (leafIndex k (fun i=>i) j)).pow_const (P.exponent/4))
  · exact measurable_const.mul ((MinimumGapChoice.blockChoice_gap_measurable
      (fun p=>lower L k p) (fun p=>upper L k p) (lower_measurable L k) (upper_measurable L k)
      cs j.succ h).pow_const (P.exponent/4))

theorem factor_sections (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (P : CanonicalCovariance.ProfileParameters) (target : Fin n→ℝ)
    (htarget : ∀ p i,(L.observations.observations p i).target=target i)
    (k : ℕ) (t : Fin k→ℝ) (p p' : X) (x x' : Fin k→HeatCircle)
    (cs : List (Fin k×Fin (k+1))) (j0 : Fin k) (A0 ν : ℝ) :
    factor L P k (separated k (p,t,x)) cs j0 A0 ν=
      factor L P k (separated k (p',t,x')) cs j0 A0 ν := by
  have hl := FixedHistoryTimeFactors.lower_sections L T hT k t p p' x x'
  have hu := FixedHistoryTimeFactors.upper_sections L T hT k t p p' x x'
  have ht := FixedHistoryTimeFactors.targets_sections L T hT target htarget k t p p' x x'
  have hchoice : OldOnlyTimeFactor.chosen L k (separated k (p,t,x)) cs=
      OldOnlyTimeFactor.chosen L k (separated k (p',t,x')) cs := by
    funext j h
    simp only [OldOnlyTimeFactor.chosen,hl,hu]
  simp only [factor,hchoice,hl,hu,ht]

/-- Every actual native deleted leaf lies beyond the true fresh gap;
the original age-gain restoration therefore needs no extra age premise. -/
theorem fresh_gap_le_leaf_age (k : ℕ) (p : History X k) (q : ℝ) (hq : 0≤q) (j : Fin k) :
    (carrier L k).terminal p-q≤targets L k p (leafIndex k (fun i=>i) j) := by
  have ht : targets L k p (leafIndex k (fun i=>i) j)=lower L k p j := by
    rw [targets,CoveredHistoryGeometry.leaf_observation L k p j]
  rw [ht]
  exact (sub_le_self _ hq).trans (terminal_le_lower L k p j)

end SHE.OmittedTimeFactor

namespace SHE.BaselineAssignmentScale
open MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories
variable {X W : Type} [MeasurableSpace X] [MeasurableSpace W] {R : ReferenceData} {n : ℕ}

theorem total_variable_measurable (L : Level R X n) (P : CanonicalCovariance.ProfileParameters)
    (k : ℕ) (p : W→History X k) (hp : Measurable p) (A0 ν : ℝ)
    (db : W→Fin k→ℝ) (hdb : Measurable db) :
    Measurable (fun w=>total L P k (p w) A0 ν (db w)) := by
  apply Finset.measurable_sum
  intro i _
  unfold scale
  split_ifs
  · exact (continuous_abs.measurable.comp ((measurable_pi_apply i.1).comp hdb)).mul
      (continuous_abs.measurable.comp ((OmittedTimeFactor.factor_measurable L P k (choices k i) i.1 A0 ν).comp hp))
  · exact measurable_const

end SHE.BaselineAssignmentScale
