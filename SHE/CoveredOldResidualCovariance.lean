module

public import SHE.PhysicalFullResidualScore
public import SHE.CoveredControlledLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2700000
noncomputable section

namespace SHE.CoveredControlledLaw
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry ControlledOldIntervals
open scoped BigOperators
local instance coveredOldResidualCovariance_periodPos : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

/-- The old intervals keep their original matrices when the full future
window is clipped at the original initial terminal time. -/
theorem old_family_eq (L : CutoffWordLevel.Level R X n) (c : Domain → ℝ)
    (k : ℕ) (p : History X k) {q : ℝ} (hq : 0 ≤ q)
    (hqt : q ≤ (carrier L k).terminal p) :
    familyCovariance (stops L k p) (targets L k p) (centers L k p) c
      (lower L k p) (upper L k p)=
      covariances L ((carrier L k).observations.observations p) c k p := by
  funext j
  exact CoveredControlledCovariance.interval_clip_upper _ c
    (hq.trans (hqt.trans (terminal_le_lower L k p j))) (upper_le_initial L k p j)

/-- The actual full residual, after removing only the fixed old
fractions, is one full stopped covariance with coefficient
profile(theta)-fixedOld. No common front fraction is removed. -/
theorem full_residual_eq_fixedReserve_ae (P : CanonicalCovariance.ProfileParameters)
    (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
    (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) μ k,
      ∀ q : ℝ,0 ≤ q → q ≤ (carrier L k).terminal p →
        fullResidualCovariance L (referenceProfile P Λ u dir) k p q=
          ControlledFixedReserve.covariance P Λ u dir
            (fixedProfile P Λ u dir (lower L k p) (upper L k p))
            (stops L k p) (targets L k p) (centers L k p) q θ := by
  let c := referenceProfile P Λ u dir
  let ref := (ControlledWordLevel.referenceData P ha Λ u dir θ).reference
  have hc : Measurable c := referenceProfile_measurable P Λ u dir
  have hb (r : Domain) : fraction P*P.lower ≤ c r ∧ c r ≤ ref r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [CoveredControlledCovariance.terminal_decomposition_ae L c hc
    (mul_pos (fraction_pos P) P.lower_pos) hb hages μ k] with p hp
  intro q hq hqt
  let Z := (carrier L k).observations.observations p
  let hi := (carrier L k).terminal p
  have hZ : ∀ i,(Z i).stop ≤ (Z i).target := RecursiveScoreSupport.carrier_ages L hages k p
  have hcref : Measurable ref := (ControlledWordLevel.referenceData P ha Λ u dir θ).reference_measurable
  have hcn (r : Domain) : 0 ≤ c r ∧ c r ≤ P.upper :=
    ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (hb r).1,
      (hb r).2.trans (ControlledProfile.profile_bounds P Λ u dir (θ,r)).2⟩
  have hrn (r : Domain) : 0 ≤ ref r-c r ∧ ref r-c r ≤ P.upper := by
    have hh := ControlledProfile.profile_bounds P Λ u dir (θ,r)
    exact ⟨sub_nonneg.mpr (hb r).2,(sub_le_self _ (hcn r).1).trans hh.2⟩
  have hsum := interval_add_profiles Z hZ c (fun r => ref r-c r) hc (hcref.sub hc)
    P.upper_nonneg P.upper_nonneg
    (fun r => by rw [abs_of_nonneg (hcn r).1];exact (hcn r).2)
    (fun r => by rw [abs_of_nonneg (hrn r).1];exact (hrn r).2) q hi
  have hsplit : intervalCovariance Z ref q hi=
      intervalCovariance Z c q hi+intervalCovariance Z (fun r => ref r-c r) q hi := by
    simpa only [add_sub_cancel] using hsum
  have hword := PhysicalIntervalCovariance.interval_eq_covariance Z ref hcref
    (ControlledWordLevel.referenceData P ha Λ u dir θ).reference_bound hZ
    ((carrier L k).stops_after p) hq hqt
  change intervalCovariance Z ref q hi=WordRecursion.covariance ref Z q hi at hword
  have ht := hp q hq hqt
  dsimp only at ht
  simp only [Fin.sum_univ_succ,GaussianFreshFraction.covariances,Fin.cases_zero,Fin.cases_succ] at ht
  have hfull : (∑ j,covariances L Z c k p j)+fullResidualCovariance L c k p q=
      stoppedCovariance (stops L k p) (targets L k p) (centers L k p) ref q := by
    calc
      _ = intervalCovariance Z c q hi+(∑ j,covariances L Z c k p j)+
          (intervalCovariance Z (fun r => ref r-c r) q hi+
            ∑ j,covariances L Z (fun r => ref r-c r) k p j) := by
        unfold fullResidualCovariance
        rw [←hword,hsplit]
        abel
      _ = _ := ht
  have hgeom (i : Fin (n+k)) : stops L k p i ≤ targets L k p i :=
    (min_le_left _ _).trans (hZ i)
  have hr := ControlledWindowDecomposition.covariance_sum_residual P Λ u dir θ
    (lower L k p) (upper L k p) (disjoint L k p)
    (stops L k p) (targets L k p) (centers L k p) hgeom hq
    (fun j => hqt.trans (terminal_le_lower L k p j))
  rw [old_family_eq L c k p hq hqt] at hr
  apply add_left_cancel
  exact hfull.trans hr.symm

end SHE.CoveredControlledLaw
