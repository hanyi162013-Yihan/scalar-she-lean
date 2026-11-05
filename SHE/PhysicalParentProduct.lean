module

public import SHE.ActiveParentSums
public import SHE.PhysicalParentIntegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace SHE.PhysicalParentGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain OrderedHeatForests NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual old-score envelope on the final stopped observation list. -/
def activeHeatProduct (Z : Fin N → Observation) (k : ℕ) (p : History P k) : ℝ :=
  ∏ j : Fin k, ∑ i ∈ IntervalHistoryEnergy.active (fun i => (Z i).stop) (PhysicalChainArrays.upper L k p j),
    ‖ProfileVariance.heatPhysical (2*((Z i).target-PhysicalChainArrays.lower L k p j))
      (Z i).center (PhysicalChainArrays.space k p j)‖

theorem activeHeatProduct_step (Z : Fin N → Observation) (k : ℕ) (p : History P (k+1)) :
    activeHeatProduct L Z (k+1) p =
      activeHeatProduct L Z k p.1 *
      (∑ i ∈ IntervalHistoryEnergy.active (fun j => (Z j).stop) ((carrier L k).terminal p.1),
        ‖ProfileVariance.heatPhysical (2*((Z i).target-(carrier L k).nodeTime p)) (Z i).center p.2.2‖) := by
  unfold activeHeatProduct
  rw [Fin.prod_univ_succ]
  simp only [PhysicalChainArrays.upper,PhysicalChainArrays.lower,PhysicalChainArrays.space,
    Fin.cases_zero,Fin.cases_succ]
  exact mul_comm _ _

/-- The physical all-order old-score heat product is exactly the genuine
ordered earlier-parent forest density. This includes the original stop
masks, arbitrary initial targets, and every actual insertion location. -/
theorem activeHeatProduct_eq_parentDensity
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (Z : Fin N → Observation) (k : ℕ) (p : History P k)
    (g : Fin (n+k) → Fin N) (hg : Function.Injective g) (hsel : Selection L Z k p g)
    (hp : StrictHistory L k p) :
    activeHeatProduct L Z k p =
      parentDensity 2 (by norm_num) k
        (fun i => ((carrier L k).observations.observations p i).target)
        (carrier_orderedTimes L hages k p hp)
        (fun i => ((carrier L k).observations.observations p i).center) := by
  induction k with
  | zero => simp only [activeHeatProduct,Fin.prod_univ_zero,parentDensity]
  | succ k ih =>
    rw [activeHeatProduct_step,node_active_heat_sum L Z g hsel hg hp.2,
      ih p.1 (fun i => g i.succ) (hg.comp (Fin.succ_injective _)) hsel.tail hp.1]
    change parentDensity 2 (by norm_num) k
        (fun i => ((carrier L k).observations.observations p.1 i).target)
        (carrier_orderedTimes L hages k p.1 hp.1)
        (fun i => ((carrier L k).observations.observations p.1 i).center)*
        (∑ j : Fin (n+k), ‖ProfileVariance.heatPhysical
          (2*(((carrier L k).observations.observations p.1 j).target-(carrier L k).nodeTime p))
          ((carrier L k).observations.observations p.1 j).center p.2.2‖) = _
    simp only [parentDensity,add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [NativeHeatAction.edge,NativeHeatSpan.kernel_eq_physical]
    change ‖ProfileVariance.heatPhysical
      (2*(((carrier L k).observations.observations p.1 j).target-(carrier L k).nodeTime p))
      ((carrier L k).observations.observations p.1 j).center p.2.2‖ =
      ‖ProfileVariance.heatPhysical
      (2*(((carrier L k).observations.observations p.1 j).target-((carrier L k).nodeTime p+0)))
      ((carrier L k).observations.observations p.1 j).center p.2.2‖
    rw [add_zero]

end SHE.PhysicalParentGeometry
