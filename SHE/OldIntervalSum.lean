module

public import SHE.OldIntervalGaussian
public import SHE.ControlledReservedWord

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.OldIntervalCovariance
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement GaussianRangeSmooth
  StoppedGaussianFeatures StoppedFourier
open scoped Topology BigOperators Matrix.Norms.L2Operator
local instance oldIntervalSum_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}

def sumProfile (c : Domain → ℝ) (lo hi : Fin r → ℝ) (p : Domain) : ℝ :=
  ∑ j, intervalProfile c (lo j) (hi j) p

theorem measurable_sumProfile {c : Domain → ℝ} (hc : Measurable c) (lo hi : Fin r → ℝ) :
    Measurable (sumProfile c lo hi) :=
  Finset.measurable_sum Finset.univ (fun j _ => measurable_intervalProfile hc (lo j) (hi j))

/-- Disjoint old intervals consume at most one copy of the old reference
profile. The fixed positive split therefore costs no factor in the order. -/
theorem sumProfile_bounds (c : Domain → ℝ) (hc0 : ∀ p, 0 ≤ c p) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j) (p : Domain) :
    0 ≤ sumProfile c lo hi p ∧ sumProfile c lo hi p ≤ c p := by
  classical
  by_cases hp : ∃ j, p ∈ timeSet (lo j) (hi j)
  · obtain ⟨j, hj⟩ := hp
    have he : sumProfile c lo hi p = c p := by
      unfold sumProfile
      rw [Finset.sum_eq_single j]
      · exact Set.indicator_of_mem hj c
      · intro k hk hkj
        have hn : p ∉ timeSet (lo k) (hi k) := by
          intro hpk
          rcases hdisjoint j k (Ne.symm hkj) with h | h <;>
            have hjt := hj.1 <;> have hkt := hpk.1 <;> linarith [hjt.1, hjt.2, hkt.1, hkt.2]
        exact Set.indicator_of_notMem hn c
      · simp
    rw [he]
    exact ⟨hc0 p, le_rfl⟩
  · have he : sumProfile c lo hi p = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact Set.indicator_of_notMem (fun h => hp ⟨j, h⟩) c
    rw [he]
    exact ⟨le_rfl, hc0 p⟩

/-- The original full observation covariance of the fixed old fraction is
the sum of the actual interval covariance matrices. -/
theorem covariance_sumProfile (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (c : Domain → ℝ) (hc : Measurable c)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p, |c p| ≤ M) (lo hi : Fin r → ℝ) :
    stoppedCovariance σ target center (sumProfile c lo hi) 0 =
      ∑ j, familyCovariance σ target center c lo hi j := by
  ext i k
  rw [Matrix.sum_apply]
  change (∫ p, (∑ j, intervalProfile c (lo j) (hi j) p) * stoppedRow σ target center p i *
      stoppedRow σ target center p k ∂historyMeasure 0) =
    ∑ j, ∫ p, intervalProfile c (lo j) (hi j) p * stoppedRow σ target center p i *
      stoppedRow σ target center p k ∂historyMeasure 0
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  intro j hj
  apply StoppedCovarianceSplit.covariance_entry_integrable σ target center hages 0
    (measurable_intervalProfile hc (lo j) (hi j))
  intro p
  by_cases hp : p ∈ timeSet (lo j) (hi j)
  · simpa only [intervalProfile, Set.indicator_of_mem hp] using hb p
  · simpa only [intervalProfile, Set.indicator_of_notMem hp, abs_zero] using hM

theorem decreasing_intervals_disjoint (t : Fin (r + 1) → ℝ) (ht : StrictAnti t)
    (j k : Fin r) (hjk : j ≠ k) :
    t j.castSucc ≤ t k.succ ∨ t k.castSucc ≤ t j.succ := by
  rcases lt_or_gt_of_ne hjk with h | h
  · right
    apply ht.antitone
    exact_mod_cast (show j.val + 1 ≤ k.val by omega)
  · left
    apply ht.antitone
    exact_mod_cast (show k.val + 1 ≤ j.val by omega)

end SHE.OldIntervalCovariance
