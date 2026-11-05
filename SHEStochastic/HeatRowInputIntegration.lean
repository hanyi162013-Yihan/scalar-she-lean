module

public import SHEStochastic.HeatRowPhysicalIntegration
public import SHEStochastic.UnboundedHeatJointFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.HeatRowInputIntegration
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open HeatParameterPullback UnboundedHeatFamily
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
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)

/-- The spatial Bochner integral of the actual predictable-input family
has its literal pointwise row-average representative. Joint integrability
is derived rather than assumed. The predictable trim is handled before
transporting the conclusion back to the original time-probability measure. -/
theorem integral_ae_trim (t : ShortTime) (ht : t.val ≤ H)
    (ρ : Measure HeatCircle) [IsFiniteMeasure ρ] :
    (∫ a : HeatCircle, input F U hU hG hβ hβ1 μ H
      ⟨t.val, t.property.1⟩ ht t.property.2 a hbound ∂ρ) =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      fun p ↦ ∫ a : HeatCircle, family F U hU hG hβ hβ1 ⟨t.val, t.property.1⟩ a p ∂ρ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let η := (energyMeasure μ H).trim (predictable_le_product F)
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  letI : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let K := fun a : HeatCircle ↦ input F U hU hG hβ hβ1 μ H
    ⟨t.val, t.property.1⟩ ht t.property.2 a hbound
  let raw := fun z : HeatCircle × (ℝ≥0 × Ω) ↦ family F U hU hG hβ hβ1 ⟨t.val, t.property.1⟩ z.1 z.2
  have hK : Integrable K ρ := HeatRowPhysicalIntegration.integrable_input F U hU hG hβ hβ1 μ H hbound t ht ρ
  have hraw : AEStronglyMeasurable raw (ρ.prod η) :=
    (UnboundedHeatJointFamily.stronglyMeasurable F U hU hG hβ hβ1 ⟨t.val, t.property.1⟩).aestronglyMeasurable
  have he : ∀ᵐ a ∂ρ, K a =ᵐ[η] fun p ↦ raw (a, p) :=
    Eventually.of_forall fun a ↦ (memLp F U hU hG hβ hβ1 μ H
      ⟨t.val, t.property.1⟩ ht t.property.2 a hbound).coeFn_toLp
  have hi := LpVersionIntegration.integrable η ρ K hK raw hraw he
  exact LpIntegralFubini.integral_ae η ρ K hK raw hi he

theorem integral_ae (t : ShortTime) (ht : t.val ≤ H)
    (ρ : Measure HeatCircle) [IsFiniteMeasure ρ] :
    (∫ a : HeatCircle, input F U hU hG hβ hβ1 μ H
      ⟨t.val, t.property.1⟩ ht t.property.2 a hbound ∂ρ) =ᵐ[energyMeasure μ H]
      fun p ↦ ∫ a : HeatCircle, family F U hU hG hβ hβ1 ⟨t.val, t.property.1⟩ a p ∂ρ :=
  ae_eq_of_ae_eq_trim (integral_ae_trim F U hU hG hβ hβ1 μ H hbound t ht ρ)

/-- Signed spatial averages keep their literal row representatives in
the predictable L2 space. This includes both real Fourier components. -/
theorem weighted_integral_ae_trim (t : ShortTime) (ht : t.val ≤ H)
    (ρ : Measure HeatCircle) [IsFiniteMeasure ρ] (w : C(HeatCircle, ℝ)) :
    (∫ a : HeatCircle, w a • input F U hU hG hβ hβ1 μ H
      ⟨t.val, t.property.1⟩ ht t.property.2 a hbound ∂ρ) =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      fun p ↦ ∫ a : HeatCircle, w a • family F U hU hG hβ hβ1 ⟨t.val, t.property.1⟩ a p ∂ρ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let η := (energyMeasure μ H).trim (predictable_le_product F)
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  letI : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let K := fun a : HeatCircle ↦ input F U hU hG hβ hβ1 μ H
    ⟨t.val, t.property.1⟩ ht t.property.2 a hbound
  let raw := fun z : HeatCircle × (ℝ≥0 × Ω) ↦
    w z.1 • family F U hU hG hβ hβ1 ⟨t.val, t.property.1⟩ z.1 z.2
  have hK : Integrable K ρ := HeatRowPhysicalIntegration.integrable_input F U hU hG hβ hβ1 μ H hbound t ht ρ
  have hwK : Integrable (fun a ↦ w a • K a) ρ := hK.bdd_smul (𝕜 := ℝ) (φ := w) ‖w‖
    w.continuous.measurable.aestronglyMeasurable (Eventually.of_forall w.norm_coe_le_norm)
  have hraw : AEStronglyMeasurable raw (ρ.prod η) :=
    ((w.continuous.measurable.comp measurable_fst).stronglyMeasurable.smul
      (UnboundedHeatJointFamily.stronglyMeasurable F U hU hG hβ hβ1 ⟨t.val, t.property.1⟩)).aestronglyMeasurable
  have he : ∀ᵐ a ∂ρ, w a • K a =ᵐ[η] fun p ↦ raw (a, p) := by
    apply Eventually.of_forall
    intro a
    filter_upwards [Lp.coeFn_smul (w a) (K a),
      (memLp F U hU hG hβ hβ1 μ H ⟨t.val, t.property.1⟩ ht t.property.2 a hbound).coeFn_toLp] with p hs hi
    exact hs.trans (congrArg (fun v ↦ w a • v) hi)
  have hi := LpVersionIntegration.integrable η ρ (fun a ↦ w a • K a) hwK raw hraw he
  exact LpIntegralFubini.integral_ae η ρ (fun a ↦ w a • K a) hwK raw hi he

end SHEStochastic.HeatRowInputIntegration
