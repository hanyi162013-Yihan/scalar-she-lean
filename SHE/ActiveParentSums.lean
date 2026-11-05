module

public import SHE.PhysicalParentGeometry
public import SHE.IntervalHistoryEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.PhysicalParentGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain OrderedHeatForests
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N M : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- Actual stopped active sums equal the original selected earlier
frame. No physical observation is inserted, removed, or duplicated. -/
theorem active_sum_eq_selected (σ : Fin N → ℝ) {lo hi : ℝ} (hgap : lo < hi)
    (f : Fin M → Fin N) (hf : Function.Injective f)
    (hs : ∀ j, hi ≤ σ (f j)) (ho : ∀ i, i ∉ Set.range f → σ i ≤ lo) (F : Fin N → ℝ) :
    (∑ i ∈ IntervalHistoryEnergy.active σ hi, F i) = ∑ j : Fin M, F (f j) := by
  classical
  have hset : IntervalHistoryEnergy.active σ hi = Finset.univ.image f := by
    ext i
    simp only [IntervalHistoryEnergy.active,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_image,true_and]
    constructor
    · intro hsi
      by_contra hn
      exact (not_le.mpr hgap) (hsi.trans (ho i hn))
    · rintro ⟨j,rfl⟩
      exact hs j
  rw [hset,Finset.sum_image]
  exact fun i _ j _ h => hf h

theorem node_active_sum {k : ℕ} {p : History P (k+1)}
    (Z : Fin N → Observation) (g : Fin (n+k+1) → Fin N)
    (hsel : Selection L Z (k+1) p g) (hg : Function.Injective g)
    (hp : Interior L k p) (F : Fin N → ℝ) :
    (∑ i ∈ IntervalHistoryEnergy.active (fun j => (Z j).stop) ((carrier L k).terminal p.1), F i) =
      ∑ j : Fin (n+k), F (g j.succ) := by
  have ht : (carrier L k).nodeTime p=p.2.1 := ClippedCovariance.clip_eq ⟨hp.1.le,hp.2.le⟩
  apply active_sum_eq_selected (fun j => (Z j).stop) (lo := (carrier L k).nodeTime p)
    (by rw [ht]; exact hp.2) (fun j => g j.succ) (hg.comp (Fin.succ_injective _))
  · intro j
    rw [hsel.tail.observations j]
    exact (carrier L k).stops_after p.1 j
  · exact fun i hi => Selection.omitted_tail L hsel i hi

theorem node_active_heat_sum {k : ℕ} {p : History P (k+1)}
    (Z : Fin N → Observation) (g : Fin (n+k+1) → Fin N)
    (hsel : Selection L Z (k+1) p g) (hg : Function.Injective g) (hp : Interior L k p) :
    (∑ i ∈ IntervalHistoryEnergy.active (fun j => (Z j).stop) ((carrier L k).terminal p.1),
      ‖ProfileVariance.heatPhysical (2*((Z i).target-(carrier L k).nodeTime p)) (Z i).center p.2.2‖) =
      ∑ j : Fin (n+k), ‖ProfileVariance.heatPhysical
        (2*(((carrier L k).observations.observations p.1 j).target-(carrier L k).nodeTime p))
        ((carrier L k).observations.observations p.1 j).center p.2.2‖ := by
  rw [node_active_sum L Z g hsel hg hp]
  simp only [hsel.tail.observations]

end SHE.PhysicalParentGeometry
