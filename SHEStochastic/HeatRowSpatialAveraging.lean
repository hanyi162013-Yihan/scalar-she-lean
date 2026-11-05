module

public import SHEStochastic.UnboundedHeatFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.HeatRowSpatialAveraging
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open UnboundedHeatFamily
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)

theorem row_operator (T : ℝ≥0) (a : HeatCircle) (p : ℝ≥0 × Ω) :
    family F U hU hG hβ hβ1 T a p =
      ContinuousKernelLpAction.operator haarAddCircle
        (HolderCoefficientIntegrability.coefficient hβ hβ1.le hG (U p))
        (RealCausalHeatKernel.value a ((T : ℝ) - (p.1 : ℝ))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HolderStateRows.row_operator U hU hG hβ hβ1.le (kernelFamily T a) p

/-- Spatial smoothing of the literal unbounded-coefficient stochastic
row adds its heat age and leaves its original causal time cutoff intact.
The coefficient is only an L2 class, and may be vector or matrix valued. -/
theorem spatial_average (T δ : ℝ≥0) (hδ : 0 < δ) (x : HeatCircle) (p : ℝ≥0 × Ω) :
    (∫ a : HeatCircle, RealCausalHeatKernel.value x δ a • family F U hU hG hβ hβ1 T a p ∂haarAddCircle) =
      if p.1 < T then family F U hU hG hβ hβ1 (T + δ) x p else 0 := by
  by_cases hp : p.1 < T
  · rw [if_pos hp]
    simp_rw [row_operator F U hU hG hβ hβ1]
    let L := ContinuousKernelLpAction.operator haarAddCircle
      (HolderCoefficientIntegrability.coefficient hβ hβ1.le hG (U p))
    let r : ℝ := (T : ℝ) - (p.1 : ℝ)
    have hr : 0 < r := sub_pos.mpr hp
    have hc : Continuous (fun a : HeatCircle ↦ RealCausalHeatKernel.value x δ a • RealCausalHeatKernel.value a r) :=
      (RealCausalHeatKernel.value x δ).continuous.smul (RealCausalHeatKernel.continuous_center hr)
    have hi : Integrable (fun a : HeatCircle ↦ RealCausalHeatKernel.value x δ a • RealCausalHeatKernel.value a r)
        haarAddCircle := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change (∫ a : HeatCircle, RealCausalHeatKernel.value x δ a • L (RealCausalHeatKernel.value a r) ∂haarAddCircle) =
      L (RealCausalHeatKernel.value x ((T + δ : ℝ≥0) - (p.1 : ℝ)))
    calc
      _ = ∫ a : HeatCircle, L (RealCausalHeatKernel.value x δ a • RealCausalHeatKernel.value a r) ∂haarAddCircle :=
        integral_congr_ae (Eventually.of_forall fun a ↦ (L.map_smul _ _).symm)
      _ = L (∫ a : HeatCircle, RealCausalHeatKernel.value x δ a • RealCausalHeatKernel.value a r ∂haarAddCircle) :=
        L.integral_comp_comm hi
      _ = L (RealCausalHeatKernel.value x ((δ : ℝ) + r)) :=
        congrArg L (RealCausalHeatKernel.integral_kernel hδ hr x)
      _ = _ := by
        congr 1
        congr 1
        dsimp [r]
        ring
  · rw [if_neg hp]
    have hz (a : HeatCircle) : family F U hU hG hβ hβ1 T a p = 0 :=
      family_zero_after F U hU hG hβ hβ1 T a p (le_of_not_gt hp)
    simp only [hz, smul_zero, integral_zero]

end SHEStochastic.HeatRowSpatialAveraging
