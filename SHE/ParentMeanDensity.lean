module

public import SHE.ScalarMeanSpatialMoments
public import SHE.PhysicalParentProduct

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ParentMeanDensity
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain OrderedHeatForests NativeHeatAction
  HistoryProductMeasure ScalarMeanEnvelope
open scoped BigOperators
local instance parentMeanDensity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The deterministic earlier-parent heat product on every history,
including collisions and nonordered histories. It is defined before any
random reference or Gaussian covariance is chosen. -/
def parentProduct : (k : ℕ)→History P k→ℝ
  | 0,_=>1
  | k+1,p=>parentProduct k p.1*nodeHeat L k p

theorem parentProduct_nonneg (k : ℕ) (p : History P k) : 0≤parentProduct L k p := by
  induction k with
  | zero=>exact zero_le_one
  | succ k ih=>exact mul_nonneg (ih p.1) (nodeHeat_nonneg L k p)

theorem parentProduct_measurable (k : ℕ) : Measurable (parentProduct L k) := by
  induction k with
  | zero=>exact measurable_const
  | succ k ih=>exact (ih.comp measurable_fst).mul (nodeHeat_measurable L k)

/-- On actual ordered histories this Borel product is exactly the
literal positive forest density, with all original target times. -/
theorem parentProduct_eq_parentDensity
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) :
    parentProduct L k p=parentDensity 2 (by norm_num) k
      (fun i=>((carrier L k).observations.observations p i).target)
      (carrier_orderedTimes L hages k p hp)
      (fun i=>((carrier L k).observations.observations p i).center) := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [parentProduct,ih p.1 hp.1]
    simp only [parentDensity,nodeHeat,add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [edge,NativeHeatSpan.kernel_eq_physical]
    change ‖ProfileVariance.heatPhysical
      (2*(((carrier L k).observations.observations p.1 i).target-(carrier L k).nodeTime p))
      ((carrier L k).observations.observations p.1 i).center p.2.2‖=
      ‖ProfileVariance.heatPhysical
      (2*(((carrier L k).observations.observations p.1 i).target-((carrier L k).nodeTime p+0)))
      ((carrier L k).observations.observations p.1 i).center p.2.2‖
    rw [add_zero]

theorem parentProduct_replaceSpace_eq
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (x : Fin k→HeatCircle) :
    parentProduct L k (replaceSpace k p x)=parentEnvelope L hages k p hp x := by
  rw [parentProduct_eq_parentDensity L hages k (replaceSpace k p x)
    ((replaceSpace_strict_iff L k p x).mpr hp)]
  unfold parentEnvelope
  congr 2
  exact replaceSpace_targets L k p x

end SHE.ParentMeanDensity
