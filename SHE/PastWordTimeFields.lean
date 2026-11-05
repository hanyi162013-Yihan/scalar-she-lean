module

public import SHE.MixedPastWordMoments
public import SHE.PhysicalAssignmentGapScale
public import SHE.SharpTimeSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastWordMoments
open Set MeasureTheory Real GaussianAssignmentBlocks GaussianFreshAssignments PhysicalAssignmentGapScale
open scoped BigOperators

/-- The actual old assignment factor depends on its original intervals
only through their gaps. In particular absolute-to-relative time shifts
do not change a selected minimum or an old root clip. -/
theorem factor_eq_plainFactor_gaps {k : ℕ} (P : CanonicalCovariance.ProfileParameters)
    (lo hi age : Fin k→ℝ) (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) (d : ℕ) :
    factor (d:=d) P lo hi age cs A0 ν=
      plainFactor P cs (fun j=>hi j-lo j) age A0 ν d := by
  unfold factor plainFactor
  congr 1
  · simp only [VectorPhysicalRoot.scale,sub_zero]
  · apply Finset.prod_congr rfl
    intro j _
    unfold NativeAssignedLeafMoments.leafScale MinimumGapChoice.blockChoice
    split_ifs <;> simp only [sub_zero]

theorem factor_measurable {X : Type*} [MeasurableSpace X] {k : ℕ}
    (P : CanonicalCovariance.ProfileParameters) (lo hi age : X→Fin k→ℝ)
    (hlo : ∀ j,Measurable (fun x=>lo x j)) (hhi : ∀ j,Measurable (fun x=>hi x j))
    (hage : ∀ j,Measurable (fun x=>age x j)) (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) (d : ℕ) :
    Measurable (fun x=>factor (d:=d) P (lo x) (hi x) (age x) cs A0 ν) := by
  have hroot : Measurable (fun x=>VectorPhysicalRoot.scale cs 0 (lo x) (hi x) A0 ν (P.lower/2) d) := by
    unfold VectorPhysicalRoot.scale
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.min (((hhi _).sub (hlo _)).pow_const (1/4:ℝ) |>.const_mul _)
  have hleaf (j : Fin k) : Measurable (fun x=>NativeAssignedLeafMoments.leafScale P cs j.succ
      (lo x) (hi x) (age x j) (MinimumGapChoice.blockChoice (lo x) (hi x) cs j.succ)) := by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs with h
    · exact measurable_const.mul ((hage j).pow_const _)
    · exact measurable_const.mul ((MinimumGapChoice.blockChoice_gap_measurable lo hi hlo hhi cs j.succ h).pow_const _)
  exact hroot.mul (Finset.measurable_prod Finset.univ (fun j _=>hleaf j))

theorem total_measurable {X : Type*} [MeasurableSpace X] {k : ℕ}
    (P : CanonicalCovariance.ProfileParameters) (lo hi age : X→Fin k→ℝ)
    (hlo : ∀ j,Measurable (fun x=>lo x j)) (hhi : ∀ j,Measurable (fun x=>hi x j))
    (hage : ∀ j,Measurable (fun x=>age x j)) (A0 ν : ℝ) (d : ℕ) :
    Measurable (fun x=>total (d:=d) P (lo x) (hi x) (age x) A0 ν) := by
  unfold total
  simp_rw [FiniteAssignmentMoments.map_sum_eq_fin]
  exact Finset.measurable_sum Finset.univ (fun i _=>continuous_abs.measurable.comp
    (factor_measurable P lo hi age hlo hhi hage _ A0 ν d))

end SHE.MixedPastWordMoments

namespace SHE.PastWordTimeFields
open Set MeasureTheory Real WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays CoveredControlledLaw PhysicalParentGeometry
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- Full literal relative-age sharp assignment sum. Empty rough blocks
keep target-base, rather than the absolute target time. -/
def total (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (A0 ν : ℝ) : ℝ :=
  MixedPastWordMoments.total (d:=n) P (fun j=>lower L k p j-R.base)
    (fun j=>upper L k p j-R.base)
    (fun j=>targets L k p (leafIndex k (fun i=>i) j)-R.base) A0 ν

theorem total_nonneg (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k) (A0 ν : ℝ) :
    0≤total L P k p A0 ν := MixedPastWordMoments.total_nonneg P _ _ _ A0 ν

theorem total_measurable (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (A0 ν : ℝ) :
    Measurable (fun p=>total L P k p A0 ν) :=
  MixedPastWordMoments.total_measurable P _ _ _
    (fun j=>(lower_measurable L k j).sub_const R.base)
    (fun j=>(upper_measurable L k j).sub_const R.base)
    (fun j=>((carrier L k).observations.target_measurable _).sub_const R.base) A0 ν n

theorem total_replaceSpace (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (A0 ν : ℝ) (x : Fin k→StoppedFourier.HeatCircle) :
    total L P k (replaceSpace k p x) A0 ν=total L P k p A0 ν := by
  have ht : targets L k (replaceSpace k p x)=targets L k p := replaceSpace_targets L k p x
  unfold total
  simp only [PhysicalWordTimeScale.lower_replaceSpace,PhysicalWordTimeScale.upper_replaceSpace,
    ht]

end SHE.PastWordTimeFields
