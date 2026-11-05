module

public import SHEStochastic.PhysicalRootHeatRows
public import SHEStochastic.BoundedMildAllHeatObservations
public import SHEStochastic.NoiseRestriction
public import SHE.PredictableScalarHaarRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.PhysicalOriginalHeatRows
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open SHE.OrthogonalItoChannels
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  SHE.FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

abbrev Noise := Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))

/-- Physical scalar noise occupies the first original channel. -/
def embedding : Noise →ₗᵢ[ℝ] Both RealL2 := left.comp NativePhysicalState.pull

theorem push_original (D : SmoothApproximation.ScalarData) (u v : RealL2) :
    NativePhysicalState.push (ScalarSplittingInputs.originalInput haarAddCircle
      (ScalarHaarRotation.scalar D u) (ScalarHaarRotation.scalar_measurable D u)
      D.upper (ScalarHaarRotation.scalar_bound D u) v) =ᵐ[haarAddCircle]
        fun y ↦ D.coefficient (NativePhysicalState.push u y) * NativePhysicalState.push v y := by
  let z := ScalarSplittingInputs.originalInput haarAddCircle
    (ScalarHaarRotation.scalar D u) (ScalarHaarRotation.scalar_measurable D u)
    D.upper (ScalarHaarRotation.scalar_bound D u) v
  have hz := RealMultiplier.operator_ae haarAddCircle
    (ScalarHaarRotation.scalar D u) (ScalarHaarRotation.scalar_measurable D u) |D.upper|
    ((ScalarHaarRotation.scalar_bound D u).mono (fun y hy ↦ by
      simpa only [Real.norm_eq_abs] using hy.trans (le_abs_self D.upper))) v
  have hh := (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).quasiMeasurePreserving.ae hz
  have hu := (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).quasiMeasurePreserving.ae
    (PredictableScalarField.unitField_ae (fun u : RealL2 ↦ u) u)
  filter_upwards [NativePhysicalState.push_ae z, hh, hu,
    NativePhysicalState.push_ae u, NativePhysicalState.push_ae v] with y hp hh hu hU hv
  change z (CircleNormalization.scale (2 * Real.pi) 1 y) = _ at hh
  rw [hp, hh]
  change D.coefficient (PredictableScalarField.unitField (fun u : RealL2 ↦ u)
    (u, CircleNormalization.scale (2 * Real.pi) 1 y)) * _ = _
  rw [hu, ← hU, ← hv]

theorem push_original_heat (D : SmoothApproximation.ScalarData) (u : RealL2)
    {r : ℝ} (hr : 0 < r) (x : HeatCircle) :
    NativePhysicalState.push (ScalarSplittingInputs.originalInput haarAddCircle
      (ScalarHaarRotation.scalar D u) (ScalarHaarRotation.scalar_measurable D u)
      D.upper (ScalarHaarRotation.scalar_bound D u) (ScalarHaarHeatRows.test r x)) =ᵐ[haarAddCircle]
        fun y ↦ RealCausalHeatKernel.value x r y * D.coefficient (NativePhysicalState.push u y) := by
  filter_upwards [push_original D u (ScalarHaarHeatRows.test r x), PhysicalRootHeatRows.push_test hr x]
    with y hp ht
  rw [hp, ht, mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (D : SmoothApproximation.ScalarData)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {C β : ℝ≥0} (hG : HolderWith C β D.coefficient) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖D.coefficient z‖ ≤ B)

include hG hβ hβ1 hb in
/-- Equality of genuine predictable L2 inputs, not just covariance:
the original signed coefficient row is the embedded averaged heat row. -/
theorem input_eq (T δ : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1)
    (hδ : 0 < δ) (x : HeatCircle) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F)) embedding
      (SmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        T δ hTH hT hδ x) =
      PredictableScalarHaarRotation.originalRow F μ H D (Function.uncurry W) hW
        (T := ((T+δ : ℝ≥0) : ℝ)) (t := (T : ℝ)) (by exact_mod_cast lt_add_of_pos_right T hδ) x := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim (L2HilbertSum.lift_ae
    ((energyMeasure μ H).trim (predictable_le_product F)) embedding
      (SmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        T δ hTH hT hδ x)),
    PredictableScalarHaarRotation.originalRow_ae F μ H D (Function.uncurry W) hW
      (T := ((T+δ : ℝ≥0) : ℝ)) (t := (T : ℝ)) (by exact_mod_cast lt_add_of_pos_right T hδ) x,
    SmoothedBoundedHeatInput.spatial_ae F (UnboundedNativeHeatEquation.physical W)
      (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
      T δ hTH hT hδ x] with p hl ho hs
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
    have hz : SmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        T δ hTH hT hδ x p = 0 := by
      apply Lp.ext
      filter_upwards [hs, Lp.coeFn_zero (E := ℝ) (p := 2) (haarAddCircle (T := 2 * Real.pi))] with y hy hz
      rw [if_neg ht'] at hy
      exact hy.trans hz.symm
    rw [hz, map_zero]

end SHEStochastic.PhysicalOriginalHeatRows
