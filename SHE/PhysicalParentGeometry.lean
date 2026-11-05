module

public import SHE.ParentHeatIntegration
public import SHE.PhysicalChainArrays

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PhysicalParentGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain OrderedHeatForests
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def StrictHistory : (k : ℕ) → History P k → Prop
  | 0,_ => True
  | k+1,p => StrictHistory k p.1 ∧ Interior L k p

theorem carrier_orderedTimes
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) :
    OrderedTimes k (fun i => ((carrier L k).observations.observations p i).target) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨ih p.1 hp.1,?_⟩
    intro i
    have htime : (carrier L k).nodeTime p = p.2.1 := ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
    change (carrier L k).nodeTime p+0 < ((carrier L k).observations.observations p.1 i).target
    rw [add_zero,htime]
    exact hp.2.2.trans_le (((carrier L k).stops_after p.1 i).trans
      (RecursiveScoreSupport.carrier_ages L hages k p.1 i))

theorem carrier_centers_eq_values (k : ℕ) (p : History P k) :
    (fun i => ((carrier L k).observations.observations p i).center) =
      values (fun i => (L.observations.observations (rootParameter k p) i).center)
        k (PhysicalChainArrays.space k p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih p.1) j

theorem carrier_rootTargets (k : ℕ) (p : History P k) :
    rootValues k (fun i => ((carrier L k).observations.observations p i).target) =
      fun i => (L.observations.observations (rootParameter k p) i).target := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih p.1

theorem carrier_targets_after {k : ℕ} (p : History P k)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    {q : ℝ} (hq : q < (carrier L k).terminal p) :
    ∀ i, q < ((carrier L k).observations.observations p i).target := by
  intro i
  exact hq.trans_le (((carrier L k).stops_after p i).trans
    (RecursiveScoreSupport.carrier_ages L hages k p i))

/-- Every nonordered history has literal zero recursive word weight;
the spatial forest estimate is therefore only needed on strict histories. -/
theorem weight_zero_of_not_strict (k : ℕ) (p : History P k) (hp : ¬ StrictHistory L k p) :
    UncutSmoothWords.weight L k p = 0 := by
  induction k with
  | zero => exact False.elim (hp trivial)
  | succ k ih =>
    change UncutSmoothWords.weight L k p.1 * ‖row L k p‖^2 = 0
    by_cases hprev : StrictHistory L k p.1
    · have hn : ¬ Interior L k p := fun h => hp ⟨hprev,h⟩
      simp only [row,hn,ite_false,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero]
    · rw [ih p.1 hprev,zero_mul]

theorem test_zero_of_not_strict (k : ℕ) (p : History P k) (hp : ¬ StrictHistory L k p) :
    UncutSmoothWords.test L k p = 0 := by
  rw [UncutSmoothWords.test_eq_weight_normalized,weight_zero_of_not_strict L k p hp,zero_smul]

end SHE.PhysicalParentGeometry
