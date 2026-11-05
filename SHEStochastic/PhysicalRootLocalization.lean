module

public import SHEStochastic.PhysicalRootHeatRows
public import SHEStochastic.UnboundedNativeHeatEquation

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.PhysicalRootLocalization
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  {a G : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ}
  (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
  (hsquare : ∀ z, a z = (G z)^2) (hGpos : ∀ z, 0 ≤ G z)
  {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
  (hf : StronglyMeasurable[F.predictable] (ContinuousHeatMild.coefficientFunction ha hell hb W))

local notation "f" => ContinuousHeatMild.coefficientFunction ha hell hb W
local notation "hcap" => hell.le.trans ((hb 0).1.trans (hb 0).2)

include hsquare hGpos hcW in
/-- The decoded physical heat input agrees before the ACTUAL spatial
L2 exit with the localized input defining the native weak equation. -/
theorem agrees_before_exit (N : ℕ) (T t : ℝ≥0) (ht : (t : ℝ) < T)
    (hTH : T ≤ H) (hT1 : (T : ℝ) ≤ 1) (x : HeatCircle) :
    ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0) < UnboundedNativeHeatEquation.exit W N p.2 →
      NativePhysicalObservationInput.decode F μ H hell f hf
        (NativeObservationProcess.process F μ H hell hcap f hf ht x) p =
      StoppedItoInputs.stop F μ H t
        (UnboundedNativeHeatEquation.row F μ H W hW hG hβ hβ1 N T hTH hT1 x) p := by
  let U := UnboundedNativeHeatEquation.physical W
  have hU := UnboundedNativeHeatEquation.physical_predictable F W hW
  let Uloc := UnboundedL2Localization.state U N
  have hUp := UnboundedL2Localization.predictable F U hU N
  let v := UnboundedNativeHeatEquation.row F μ H W hW hG hβ hβ1 N T hTH hT1 x
  have hv := UnboundedHeatFamily.input_ae F Uloc hUp hG hβ hβ1 μ H T hTH hT1 x
    (UnboundedL2Localization.history_bound U μ H N)
  filter_upwards [NativePhysicalObservationInput.observation_ae F μ H hell f hf hcap ht x,
    StoppedItoInputs.stop_ae F μ H t v, hv] with p hp hs hv hbefore
  change v p = _ at hv
  rw [hp, hs]
  by_cases hpt : (p.1 : ℝ) < t
  · rw [ite_eq_left hpt, Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) t from hpt), hv]
    have hstate : Uloc p = U p := UnboundedL2Localization.agrees_before_exit U
      (UnboundedNativeHeatEquation.physical_continuous W hcW) N p hbefore
    apply Lp.ext
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    filter_upwards [PhysicalRootHeatRows.coefficient_heat ha hell hb hsquare hGpos
      (W p.1 p.2) (sub_pos.mpr (hpt.trans ht)) x,
      HolderStateRows.row_ae Uloc hUp hG hβ hβ1.le (UnboundedHeatFamily.kernelFamily T x) p]
      with y hroot hrow
    change (NativePhysicalState.push (RealRootMultiplier.action hell (f p)
      (ScalarHaarHeatRows.test ((T : ℝ)-(p.1 : ℝ)) x))) y = _ at hroot
    change _ = HolderStateRows.row Uloc hUp hG hβ hβ1.le (UnboundedHeatFamily.kernelFamily T x) p y
    rw [hroot, hrow, hstate]
    rfl
  · rw [ite_eq_right hpt,
      Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) t from hpt)]

end SHEStochastic.PhysicalRootLocalization
