module

public import SHEStochastic.PhysicalRootHeatRows
public import SHEStochastic.GlobalBoundedMildAllHeatObservations
public import SHEStochastic.PhysicalOriginalHeatRows
public import SHEStochastic.NoiseRestriction
public import SHE.PredictableScalarHaarRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalPhysicalOriginalHeatRows
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open SHE.OrthogonalItoChannels PhysicalOriginalHeatRows
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  SHE.FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (D : SmoothApproximation.ScalarData)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {C β : ℝ≥0} (hG : HolderWith C β D.coefficient) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖D.coefficient z‖ ≤ B)

include hG hβ hβ1 hb in
/-- Equality of genuine predictable L2 inputs, not just covariance:
the original signed coefficient row is the embedded averaged heat row. -/
theorem input_eq (T δ : ℝ≥0) (hTH : T ≤ H) (hH : 0<H)
    (hδ : 0 < δ) (x : HeatCircle) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F)) embedding
      (GlobalSmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        T δ hTH hH hδ x) =
      PredictableScalarHaarRotation.originalRow F μ H D (Function.uncurry W) hW
        (T := ((T+δ : ℝ≥0) : ℝ)) (t := (T : ℝ)) (by exact_mod_cast lt_add_of_pos_right T hδ) x := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim (L2HilbertSum.lift_ae
    ((energyMeasure μ H).trim (predictable_le_product F)) embedding
      (GlobalSmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        T δ hTH hH hδ x)),
    PredictableScalarHaarRotation.originalRow_ae F μ H D (Function.uncurry W) hW
      (T := ((T+δ : ℝ≥0) : ℝ)) (t := (T : ℝ)) (by exact_mod_cast lt_add_of_pos_right T hδ) x,
    GlobalSmoothedBoundedHeatInput.spatial_ae F (UnboundedNativeHeatEquation.physical W)
      (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
      T δ hTH hH hδ x] with p hl ho hs
  rw [hl, ho]
  by_cases ht : (p.1 : ℝ) < (T : ℝ)
  · rw [if_pos ht]
    have ht' : p.1 < T := by exact_mod_cast ht
    change left (NativePhysicalState.pull _) = left _
    congr 1
    apply NativePhysicalState.push.injective
    rw [NativePhysicalState.push_pull]
    apply Lp.ext
    filter_upwards [hs, push_original_heat D (W p.1 p.2)
      (sub_pos.mpr (ht.trans (by exact_mod_cast lt_add_of_pos_right T hδ))) x] with y hs hp
    rw [if_pos ht'] at hs
    exact hs.trans hp.symm
  · rw [if_neg ht]
    have ht' : ¬p.1 < T := by exact_mod_cast ht
    have hz : GlobalSmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        T δ hTH hH hδ x p = 0 := by
      apply Lp.ext
      filter_upwards [hs, Lp.coeFn_zero (E := ℝ) (p := 2) (haarAddCircle (T := 2 * Real.pi))] with y hy hz
      rw [if_neg ht'] at hy
      exact hy.trans hz.symm
    rw [hz, map_zero]

end SHEStochastic.GlobalPhysicalOriginalHeatRows
