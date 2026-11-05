module

public import SHEStochastic.GlobalPhysicalOriginalHeatRows
public import SHEStochastic.NoiseRestriction
public import SHE.SingleNativeHeatEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalBoundedNativeSingleEquation
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
local instance : MeasurableSpace PhysicalOriginalHeatRows.Noise := borel _
local instance : BorelSpace PhysicalOriginalHeatRows.Noise := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (D : SmoothApproximation.ScalarData)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {C β : ℝ≥0} (hG : HolderWith C β D.coefficient) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖D.coefficient z‖ ≤ B)

/-- The single-channel identity is a projection of the checked original
row equality; no heat-kernel or coefficient estimate is repeated. -/
theorem input_eq (T δ : ℝ≥0) (hTH : T ≤ H) (hH : 0<H)
    (hδ : 0 < δ) (x : HeatCircle) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F)) NativePhysicalState.push
      (SingleNativeHeatEquation.row F μ H D (Function.uncurry W) hW
        (T := ((T+δ : ℝ≥0) : ℝ)) (t := (T : ℝ)) (by exact_mod_cast lt_add_of_pos_right T hδ) x) =
      GlobalSmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
        (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
        T δ hTH hH hδ x := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let u := GlobalSmoothedBoundedHeatInput.input F (UnboundedNativeHeatEquation.physical W)
    (UnboundedNativeHeatEquation.physical_predictable F W hW) hG hβ hβ1.le B hb μ H
    T δ hTH hH hδ x
  have hi := GlobalPhysicalOriginalHeatRows.input_eq F μ H D W hW hG hβ hβ1 B hb T δ hTH hH hδ x
  change L2HilbertSum.lift _ NativePhysicalState.push
    (((WithLp.fstL 2 ℝ RealL2 RealL2).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product F))) _) = u
  rw [← hi]
  apply Lp.ext
  filter_upwards [L2HilbertSum.lift_ae ((energyMeasure μ H).trim (predictable_le_product F))
      NativePhysicalState.push (((WithLp.fstL 2 ℝ RealL2 RealL2).compLpL 2
        ((energyMeasure μ H).trim (predictable_le_product F)))
          (L2HilbertSum.lift _ PhysicalOriginalHeatRows.embedding u)),
    (WithLp.fstL 2 ℝ RealL2 RealL2).coeFn_compLpL
      (L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F))
        PhysicalOriginalHeatRows.embedding u),
    L2HilbertSum.lift_ae ((energyMeasure μ H).trim (predictable_le_product F))
      PhysicalOriginalHeatRows.embedding u] with p hl hf he
  rw [hl, hf, he]
  exact NativePhysicalState.push_pull _

/-- A physical native mild solution gives the original one-noise
equation on the unit-circle convention, with exactly the same integral. -/
theorem equation (hH : 0<H)
    (J : StandardTerminalIto (C := PhysicalOriginalHeatRows.Noise) (E := ℝ) F μ H)
    (u₀ : RealL2) (ξ : Ω → RealL2) (hξ : ξ =ᵐ[μ] fun _ ↦ u₀)
    (hMild : GlobalBoundedFourierRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb hH J ξ) :
    SingleNativeHeatEquation.Equation F μ H D (restrictNoise J NativePhysicalState.push) u₀ W hW := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  intro q hq ε hε x
  let δ : ℝ≥0 := ⟨ε, hε.le⟩
  have hδε : (δ : ℝ) = ε := rfl
  have hδ : 0 < δ := hε
  have ho := GlobalBoundedMildAllHeatObservations.observation F μ H W hW hG hβ hβ1 B hb hH J ξ hMild
    q δ hq hδ x
  rw [← input_eq F μ H D W hW hG hβ hβ1 B hb q δ hq hH hδ x] at ho
  have hJ (u : Process (E := RealL2) F μ H) :
      (restrictNoise J NativePhysicalState.push).integral u =
        J.integral (L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F))
          NativePhysicalState.push u) := rfl
  filter_upwards [ho, hξ] with ω ho hξ
  rw [hJ]
  simpa only [NNReal.coe_add, hδε, hξ] using ho

def data (hH : 0<H)
    (J : StandardTerminalIto (C := PhysicalOriginalHeatRows.Noise) (E := ℝ) F μ H)
    (u₀ : RealL2) (ξ : Ω → RealL2) (hξ : ξ =ᵐ[μ] fun _ ↦ u₀)
    (hc : ∀ ω, Continuous (fun t ↦ W t ω))
    (hMild : GlobalBoundedFourierRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb hH J ξ) :
    SingleNativeHeatEquation.Data F μ H D (restrictNoise J NativePhysicalState.push) u₀ where
  value := W
  continuous := hc
  predictable := hW
  equation := equation F μ H D W hW hG hβ hβ1 B hb hH J u₀ ξ hξ hMild

end SHEStochastic.GlobalBoundedNativeSingleEquation
