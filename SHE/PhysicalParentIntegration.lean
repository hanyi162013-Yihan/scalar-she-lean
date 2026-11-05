module

public import SHE.PhysicalSpatialSections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalParentGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain OrderedHeatForests NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem root_target_after
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) {q : ℝ} (hq : q < (carrier L k).terminal p) (i : Fin n) :
    q < (L.observations.observations (rootParameter k p) i).target := by
  exact hq.trans_le ((terminal_le_initial L k p).trans
    ((L.stops_after (rootParameter k p) i).trans (hages (rootParameter k p) i)))

/-- Actual original-history spatial sections satisfy the full parent
product estimate. This uses the carrier's literal observation list,
including all arbitrary root stops/targets, and integrates each actual
insertion location without changing its time or original parameter. -/
theorem parent_spatial_bound
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p)
    (i : Fin (n+k)) {q : ℝ} (hq : q < (carrier L k).terminal p) (b : HeatCircle) :
    let t := fun j => ((carrier L k).observations.observations p j).target
    let ht := carrier_orderedTimes L hages k p hp
    (∫ x : Fin k → HeatCircle, parentDensity 2 (by norm_num) k t ht
        (fun j => ((carrier L k).observations.observations (replaceSpace k p x) j).center)*
      edge (4*(t i-q)) (mul_pos (by norm_num) (sub_pos.mpr (carrier_targets_after L p hages hq i)))
        (((carrier L k).observations.observations (replaceSpace k p x) i).center) b
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
      (Fintype.card (Choices n k) : ℝ)*(Real.sqrt 2)^k*
        ∑ j : Fin n, edge (4*((L.observations.observations (rootParameter k p) j).target-q))
          (mul_pos (by norm_num) (sub_pos.mpr (root_target_after L hages k p hq j)))
          ((L.observations.observations (rootParameter k p) j).center) b := by
  intro t ht
  let a : Fin n → HeatCircle := fun j => (L.observations.observations (rootParameter k p) j).center
  have hh := parent_integral_two_four_le k t ht i (carrier_targets_after L p hages hq) a b
  have hc (x : Fin k → HeatCircle) :
      (fun j => ((carrier L k).observations.observations (replaceSpace k p x) j).center) =
        values a k x := replaceSpace_centers L k p x
  have hcp (x : Fin k → HeatCircle) (j : Fin (n+k)) :
      ((carrier L k).observations.observations (replaceSpace k p x) j).center =
        values a k x j := congrFun (hc x) j
  have hr : rootValues k t = fun j => (L.observations.observations (rootParameter k p) j).target :=
    carrier_rootTargets L k p
  simpa only [hc,hcp,hr,a] using hh

end SHE.PhysicalParentGeometry
