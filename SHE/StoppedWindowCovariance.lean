module

public import SHE.PhysicalChainCovariance
public import SHE.StoppedGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.StoppedWindowCovariance
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
open StoppedGaussianFeatures OldIntervalCovariance PhysicalScoreChain
local instance periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def clipped (Z : Fin n → Observation) (hi : ℝ) : Fin n → Observation :=
  fun i => ⟨min (Z i).stop hi,(Z i).target,(Z i).center⟩

theorem global_entries (Z : Fin n → Observation) (c : Domain → ℝ) (q : ℝ) (i j : Fin n) :
    stoppedCovariance (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) c q i j =
      ∫ r : Domain, (if q ≤ r.1 then c r *
        stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) r i *
        stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) r j else 0)
        ∂volume.prod (haarAddCircle (T := 2*Real.pi)) := by
  unfold StoppedGaussianFeatures.stoppedCovariance historyMeasure
  rw [Measure.restrict_prod_eq_prod_univ, ← integral_indicator (measurableSet_Ici.prod MeasurableSet.univ)]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  simp only [Set.indicator,mem_prod,mem_Ici,mem_univ,and_true]

/-- An actual conditional time window is exactly a stopped covariance
with lower cutoff lo and stops clipped at hi. This avoids adding any
noise after the initial word horizon, even for older root targets. -/
theorem interval_eq_clipped (Z : Fin n → Observation) (c : Domain → ℝ)
    {lo hi : ℝ} (hlo : 0 ≤ lo) :
    intervalCovariance Z c lo hi =
      stoppedCovariance (fun i => min (Z i).stop hi) (fun i => (Z i).target)
        (fun i => (Z i).center) c lo := by
  ext i j
  change StoppedGaussianFeatures.stoppedCovariance (fun i => (Z i).stop) (fun i => (Z i).target)
      (fun i => (Z i).center) (intervalProfile c lo hi) 0 i j =
    StoppedGaussianFeatures.stoppedCovariance (fun i => (clipped Z hi i).stop)
      (fun i => (clipped Z hi i).target) (fun i => (clipped Z hi i).center) c lo i j
  rw [global_entries Z (intervalProfile c lo hi) 0 i j, global_entries (clipped Z hi) c lo i j]
  apply integral_congr_ae
  have hne (t : ℝ) : ∀ᵐ r : Domain ∂volume.prod (haarAddCircle (T := 2*Real.pi)), r.1 ≠ t :=
    Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne t)
  filter_upwards [hne lo,hne hi] with r hrlo hrhi
  change (if 0 ≤ r.1 then intervalProfile c lo hi r *
      stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) r i *
      stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) r j else 0) =
    (if lo ≤ r.1 then c r * stoppedRow (fun i => min (Z i).stop hi) (fun i => (Z i).target)
      (fun i => (Z i).center) r i * stoppedRow (fun i => min (Z i).stop hi)
      (fun i => (Z i).target) (fun i => (Z i).center) r j else 0)
  by_cases hrl : lo < r.1
  · have hr0 : 0 ≤ r.1 := hlo.trans hrl.le
    by_cases hrh : r.1 < hi
    · have hm : r ∈ timeSet lo hi := ⟨⟨hrl,hrh.le⟩,mem_univ _⟩
      simp only [hr0,hrl.le,ite_true,intervalProfile,Set.indicator_of_mem hm,
        stoppedRow,lt_min_iff,hrh,and_true]
    · have hrh' : hi < r.1 := lt_of_le_of_ne (le_of_not_gt hrh) hrhi.symm
      have hm : r ∉ timeSet lo hi := fun h => (not_le_of_gt hrh') h.1.2
      have hni : ¬r.1 < min (Z i).stop hi := fun h => hrh (h.trans_le (min_le_right _ _))
      simp only [hr0,hrl.le,ite_true,intervalProfile,Set.indicator_of_notMem hm,
        stoppedRow,hni,ite_false,zero_mul,mul_zero]
  · have hrl' : r.1 < lo := lt_of_le_of_ne (le_of_not_gt hrl) hrlo
    have hm : r ∉ timeSet lo hi := fun h => (not_lt_of_ge hrl'.le) h.1.1
    simp only [not_le_of_gt hrl',ite_false,intervalProfile,Set.indicator_of_notMem hm,zero_mul]
    split_ifs <;> rfl

end SHE.StoppedWindowCovariance
