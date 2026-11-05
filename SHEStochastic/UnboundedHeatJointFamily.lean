module

public import SHEStochastic.UnboundedHeatFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.UnboundedHeatJointFamily
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
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

/-- Joint spatial-parameter/predictable measurability of the literal
Hilbert rows, even for unbounded coefficients and an arbitrary original
predictable sigma algebra. The old L2-section construction is reused. -/
theorem stronglyMeasurable (T : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace HeatCircle).prod F.predictable]
      (fun z : HeatCircle × (ℝ≥0 × Ω) ↦ family F U hU hG hβ hβ1 T z.1 z.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let W (z : HeatCircle × (ℝ≥0 × Ω)) := U z.2
  have hW : StronglyMeasurable W := hU.comp_measurable measurable_snd
  let k (z : HeatCircle × (ℝ≥0 × Ω)) := RealCausalHeatKernel.value z.1 ((T : ℝ) - (z.2.1 : ℝ))
  have ht : Measurable (fun z : (HeatCircle × (ℝ≥0 × Ω)) × HeatCircle ↦ (T : ℝ) - (z.1.2.1 : ℝ)) :=
    measurable_const.sub ((PredictableClock.real_time_measurable F).comp (measurable_snd.comp measurable_fst))
  have hk : Measurable (fun z : (HeatCircle × (ℝ≥0 × Ω)) × HeatCircle ↦ k z.1 z.2) :=
    RealCausalHeatKernel.joint_center_measurable.comp ((ht.prodMk measurable_fst.fst).prodMk measurable_snd)
  have hh := HolderStateRows.stronglyMeasurable W hW hG hβ hβ1.le k hk
  convert hh using 1
  funext z
  apply Lp.ext
  filter_upwards [HolderStateRows.row_ae U hU hG hβ hβ1.le (kernelFamily T z.1) z.2,
    HolderStateRows.row_ae W hW hG hβ hβ1.le k z] with a hf hw
  exact hf.trans hw.symm

end SHEStochastic.UnboundedHeatJointFamily
