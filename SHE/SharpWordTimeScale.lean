module

public import SHE.WordTimeScaleFields
public import SHE.MinimumGapChoice

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.SharpWordTimeScale
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays CoveredHistoryGeometry CoveredControlledLaw
  GaussianCoordinates GaussianFreshAssignments GaussianAssignmentBlocks PhysicalParentGeometry
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

def chosen (k : ℕ) (p : History X k) (q : ℝ) (cs : List (Fin k×Fin (k+1)))
    (j : Fin k) (h : block (liftChoices cs) j.succ≠[]) : Fin (k+1) :=
  MinimumGapChoice.blockChoice (lowerWith L k p q) (upperWith L k p) (liftChoices cs) j.succ h

theorem chosen_mem (k : ℕ) (p : History X k) (q : ℝ) (cs : List (Fin k×Fin (k+1)))
    (j : Fin k) (h : block (liftChoices cs) j.succ≠[]) : chosen L k p q cs j h∈block (liftChoices cs) j.succ :=
  MinimumGapChoice.blockChoice_mem _ _ _ _ _

theorem chosen_gap_le (k : ℕ) (p : History X k) (q : ℝ) (cs : List (Fin k×Fin (k+1)))
    (j : Fin k) (h : block (liftChoices cs) j.succ≠[]) (i : Fin (k+1))
    (hi : i∈block (liftChoices cs) j.succ) :
    upperWith L k p (chosen L k p q cs j h)-lowerWith L k p q (chosen L k p q cs j h)≤
      upperWith L k p i-lowerWith L k p q i :=
  MinimumGapChoice.blockChoice_gap_le _ _ _ _ _ _ hi

theorem chosen_gap_pos (k : ℕ) (p : History X k) {q : ℝ} (hp : StrictHistory L k p)
    (hq : q<(carrier L k).terminal p) (cs : List (Fin k×Fin (k+1)))
    (j : Fin k) (h : block (liftChoices cs) j.succ≠[]) :
    0<upperWith L k p (chosen L k p q cs j h)-lowerWith L k p q (chosen L k p q cs j h) :=
  sub_pos.mpr (gapWith L k p hp hq _)

/-- Every Hölder block now keeps its minimum assigned gap. All root
clips and empty-block full ages are the literal existing physical ones. -/
def factor (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (q : ℝ)
    (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) : ℝ :=
  PhysicalWordTimeScale.factor L Q k p q cs (chosen L k p q cs) A0 ν

def total (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (q A0 ν : ℝ) : ℝ :=
  ((assignments (m:=k+1) (List.finRange k)).map (fun cs => |factor L Q k p q cs A0 ν|)).sum

theorem total_nonneg (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (q A0 ν : ℝ) : 0≤total L Q k p q A0 ν := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,_,rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem factor_le_total (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (q A0 ν : ℝ) (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) :
    |factor L Q k p q cs A0 ν|≤total L Q k p q A0 ν := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨cs,_,rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  · exact List.mem_map.mpr ⟨cs,hc,rfl⟩

theorem chosen_replaceSpace (k : ℕ) (p : History X k) (q : ℝ) (cs : List (Fin k×Fin (k+1)))
    (x : Fin k→HeatCircle) : chosen L k (replaceSpace k p x) q cs=chosen L k p q cs := by
  funext j h
  unfold chosen
  rw [PhysicalWordTimeScale.lowerWith_replaceSpace,PhysicalWordTimeScale.upperWith_replaceSpace]

theorem factor_replaceSpace (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (q A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) (x : Fin k→HeatCircle) :
    factor L Q k (replaceSpace k p x) q cs A0 ν=factor L Q k p q cs A0 ν := by
  unfold factor
  rw [chosen_replaceSpace]
  exact PhysicalWordTimeScale.factor_replaceSpace L Q k p q cs _ A0 ν x

theorem total_replaceSpace (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (q A0 ν : ℝ) (x : Fin k→HeatCircle) :
    total L Q k (replaceSpace k p x) q A0 ν=total L Q k p q A0 ν := by
  simp only [total,factor_replaceSpace]

theorem factor_measurable (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q : ℝ)
    (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) :
    Measurable (fun p : History X k => factor L Q k p q cs A0 ν) := by
  have hroot : Measurable (fun p : History X k =>
      VectorPhysicalRoot.scale (liftChoices cs) 0 (lowerWith L k p q) (upperWith L k p) A0 ν (Q.lower/2) n) := by
    unfold VectorPhysicalRoot.scale
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.min (((PhysicalWordTimeScale.upperWith_measurable L k _).sub
      (PhysicalWordTimeScale.lowerWith_measurable L k q _)).pow_const (1/4:ℝ) |>.const_mul _)
  have hleaf (j : Fin k) : Measurable (fun p : History X k =>
      NativeAssignedLeafMoments.leafScale Q (liftChoices cs) j.succ
        (lowerWith L k p q) (upperWith L k p) (targets L k p (leafIndex k (fun i => i) j))
        (chosen L k p q cs j)) := by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs with h
    · exact measurable_const.mul
        (((carrier L k).observations.target_measurable (leafIndex k (fun i => i) j)).pow_const (Q.exponent/4))
    · exact measurable_const.mul ((MinimumGapChoice.blockChoice_gap_measurable
        (fun p => lowerWith L k p q) (fun p => upperWith L k p)
        (PhysicalWordTimeScale.lowerWith_measurable L k q) (PhysicalWordTimeScale.upperWith_measurable L k)
        (liftChoices cs) j.succ h).pow_const (Q.exponent/4))
  exact hroot.mul (Finset.measurable_prod Finset.univ (fun j _ => hleaf j))

theorem total_measurable (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q A0 ν : ℝ) :
    Measurable (fun p : History X k => total L Q k p q A0 ν) := by
  unfold total
  rw [show (fun p : History X k => ((assignments (m:=k+1) (List.finRange k)).map
      (fun cs => |factor L Q k p q cs A0 ν|)).sum)=
      fun p => ∑ i : Fin (assignments (m:=k+1) (List.finRange k)).length,
        |factor L Q k p q ((assignments (m:=k+1) (List.finRange k)).get i) A0 ν| from
    funext (fun _ => FiniteAssignmentMoments.map_sum_eq_fin _ _)]
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    continuous_abs.measurable.comp (factor_measurable L Q k q _ A0 ν))

end SHE.SharpWordTimeScale
