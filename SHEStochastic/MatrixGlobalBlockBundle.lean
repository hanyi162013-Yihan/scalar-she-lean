module

public import SHEStochastic.MatrixGlobalBrownianPast
public import SHE.CanonicalStateDriverPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixGlobalBlockBundle
open MeasureTheory ProbabilityTheory Set SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0) (hH0 : 0<H)

/-- Recover a local block from the literal global state and anchored
driver increments. This map is filtered even at joining time zero. -/
def bundle (k : ℕ) : MatrixGlobalBlockPath.Space (n := n) H → MatrixLocalBlockChain.Space (n := n) H :=
  CanonicalFutureStateDriver.bundle (MatrixGlobalBlockPath.state H) (MatrixGlobalBlockPath.continuous H hH0)
    (MatrixGlobalBlockPath.driver H) (MatrixGlobalBlockPath.driver_continuous H hH0) ((k : ℝ≥0)*H) H

theorem measurable (k : ℕ) : Measurable (bundle (n := n) H hH0 k) :=
  CanonicalFutureStateDriver.measurable_bundle (MatrixBlockNaturalFiltration.filtration H)
    (MatrixGlobalBlockPath.state H) (MatrixGlobalBlockPath.continuous H hH0)
    (MatrixGlobalBlockPath.driver H) (MatrixGlobalBlockPath.driver_continuous H hH0)
    (fun t => (MatrixBlockProcessAdapted.state_adapted H hH0 t).measurable)
    (fun i t => (MatrixBlockProcessAdapted.driver_adapted H hH0 i t).measurable) ((k : ℝ≥0)*H) H

theorem filtered (k : ℕ) (s : ℝ≥0) :
    @Measurable (MatrixGlobalBlockPath.Space (n := n) H) (MatrixLocalBlockChain.Space (n := n) H)
      (MatrixBlockNaturalFiltration.filtration H ((k : ℝ≥0)*H+s))
      (CanonicalStateDriverFiltration.filtration H s) (bundle H hH0 k) := by
  have hm := CanonicalFutureStateDriver.adapted_past (MatrixBlockNaturalFiltration.filtration (n := n) H)
    (MatrixGlobalBlockPath.state H) (MatrixGlobalBlockPath.continuous H hH0)
    (MatrixGlobalBlockPath.driver H) (MatrixGlobalBlockPath.driver_continuous H hH0)
    (fun t => (MatrixBlockProcessAdapted.state_adapted H hH0 t).measurable)
    (fun i t => (MatrixBlockProcessAdapted.driver_adapted H hH0 i t).measurable)
    ((k : ℝ≥0)*H) H (CanonicalStateDriverFiltration.clock H s)
  have hclock : (CanonicalStateDriverFiltration.clock H s).val.toNNReal ≤ s := by
    change (min (s : ℝ) (H : ℝ)).toNNReal ≤ s
    simpa only [Real.toNNReal_coe] using
      Real.toNNReal_le_toNNReal (min_le_left (s : ℝ) (H : ℝ))
  have htime : (k : ℝ≥0)*H+(CanonicalStateDriverFiltration.clock H s).val.toNNReal≤(k : ℝ≥0)*H+s :=
    add_le_add le_rfl hclock
  have hm' := hm.mono ((MatrixBlockNaturalFiltration.filtration H).mono htime) le_rfl
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (bundle H hH0 k)
    (MeasurableSpace.comap (CanonicalStateDriverFiltration.history H s) inferInstance)≤_
  rw [MeasurableSpace.comap_comp]
  exact hm'.comap_le

variable {H hH0} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

/-- The filtered block reconstructed from the global paths is the
original selected block almost surely, on one common path event. -/
theorem bundle_ae (k : ℕ) : bundle H hH0 k =ᵐ[D.law ρ₀] fun p => p k := by
  filter_upwards [MatrixGlobalBlockPath.block D ρ₀ hH0,MatrixBlockContinuation.driver_increment D ρ₀ hH0]
    with p hp hd
  have htime (t : Icc (0 : ℝ) (H : ℝ)) : t.val.toNNReal≤H := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal t.property.2
  have hclock (t : Icc (0 : ℝ) (H : ℝ)) : CanonicalStateDriverFiltration.clock H t.val.toNNReal=t := by
    apply Subtype.ext
    change min (t.val.toNNReal : ℝ) (H : ℝ)=t.val
    rw [Real.coe_toNNReal _ t.property.1,min_eq_left t.property.2]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change MatrixGlobalBlockPath.state H ((k : ℝ≥0)*H+t.val.toNNReal) p=(p k).1 t
    rw [hp k t.val.toNNReal (htime t)]
    change (p k).1 (CanonicalStateDriverFiltration.clock H t.val.toNNReal)=(p k).1 t
    rw [hclock]
  · funext i
    apply ContinuousMap.ext
    intro t
    change MatrixGlobalBlockPath.driver H i ((k : ℝ≥0)*H+t.val.toNNReal) p-
      MatrixGlobalBlockPath.driver H i ((k : ℝ≥0)*H) p=(p k).2 i t
    rw [hd k i t.val.toNNReal (htime t)]
    change (p k).2 i (CanonicalStateDriverFiltration.clock H t.val.toNNReal)=(p k).2 i t
    rw [hclock]

theorem preserving (k : ℕ) : MeasurePreserving (bundle H hH0 k) (D.law ρ₀) (D.blockLaw ρ₀ k).toMeasure :=
  ⟨measurable H hH0 k,(Measure.map_congr (bundle_ae D ρ₀ k)).trans (D.marginals ρ₀ k)⟩

end SHEStochastic.MatrixGlobalBlockBundle
