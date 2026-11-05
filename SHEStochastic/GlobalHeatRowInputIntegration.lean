module

public import SHEStochastic.GlobalHeatRowPhysicalIntegration
public import SHEStochastic.UnboundedHeatJointFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalHeatRowInputIntegration
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open UnboundedHeatFamily
open scoped NNReal ENNReal

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : 0<H) {R : ℝ}
  (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)

include hH in
/-- The full-horizon spatial Bochner input has its literal predictable
row-average representative, before applying the stochastic integral. -/
theorem integral_ae_trim (T : ℝ≥0) (hTH : T≤H) (ρ : Measure HeatCircle) [IsFiniteMeasure ρ] :
    (∫ a : HeatCircle, UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH a hbound ∂ρ)=ᵐ[
      (energyMeasure μ H).trim (predictable_le_product F)]
      fun p ↦ ∫ a : HeatCircle, family F U hU hG hβ hβ1 T a p ∂ρ := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  let η := (energyMeasure μ H).trim (predictable_le_product F)
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  letI : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let K := fun a : HeatCircle ↦ UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H T hTH a hbound
  let raw := fun z : HeatCircle×(ℝ≥0×Ω) ↦ family F U hU hG hβ hβ1 T z.1 z.2
  have hK : Integrable K ρ := GlobalHeatRowPhysicalIntegration.integrable_input F U hU hG hβ hβ1 μ H hH hbound T hTH ρ
  have hraw : AEStronglyMeasurable raw (ρ.prod η) :=
    (UnboundedHeatJointFamily.stronglyMeasurable F U hU hG hβ hβ1 T).aestronglyMeasurable
  have he : ∀ᵐ a ∂ρ, K a=ᵐ[η] fun p ↦ raw (a,p) :=
    Eventually.of_forall fun a ↦ (UnboundedFiniteHorizonInput.memLp F U hU hG hβ hβ1 μ H T hTH a hbound).coeFn_toLp
  have hi := LpVersionIntegration.integrable η ρ K hK raw hraw he
  exact LpIntegralFubini.integral_ae η ρ K hK raw hi he

include hH in
/-- Signed spatial averages keep their literal row representatives in
the predictable L2 space. This includes both real Fourier components. -/
theorem weighted_integral_ae_trim (T : ℝ≥0) (hTH : T≤H)
    (ρ : Measure HeatCircle) [IsFiniteMeasure ρ] (w : C(HeatCircle, ℝ)) :
    (∫ a : HeatCircle, w a • UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H
      T hTH a hbound ∂ρ) =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      fun p ↦ ∫ a : HeatCircle, w a • family F U hU hG hβ hβ1 T a p ∂ρ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let η := (energyMeasure μ H).trim (predictable_le_product F)
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  letI : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let K := fun a : HeatCircle ↦ UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H
    T hTH a hbound
  let raw := fun z : HeatCircle × (ℝ≥0 × Ω) ↦
    w z.1 • family F U hU hG hβ hβ1 T z.1 z.2
  have hK : Integrable K ρ := GlobalHeatRowPhysicalIntegration.integrable_input F U hU hG hβ hβ1 μ H hH hbound T hTH ρ
  have hwK : Integrable (fun a ↦ w a • K a) ρ := hK.bdd_smul (𝕜 := ℝ) (φ := w) ‖w‖
    w.continuous.measurable.aestronglyMeasurable (Eventually.of_forall w.norm_coe_le_norm)
  have hraw : AEStronglyMeasurable raw (ρ.prod η) :=
    ((w.continuous.measurable.comp measurable_fst).stronglyMeasurable.smul
      (UnboundedHeatJointFamily.stronglyMeasurable F U hU hG hβ hβ1 T)).aestronglyMeasurable
  have he : ∀ᵐ a ∂ρ, w a • K a =ᵐ[η] fun p ↦ raw (a, p) := by
    apply Eventually.of_forall
    intro a
    filter_upwards [Lp.coeFn_smul (w a) (K a),
      (UnboundedFiniteHorizonInput.memLp F U hU hG hβ hβ1 μ H T hTH a hbound).coeFn_toLp] with p hs hi
    exact hs.trans (congrArg (fun v ↦ w a • v) hi)
  have hi := LpVersionIntegration.integrable η ρ (fun a ↦ w a • K a) hwK raw hraw he
  exact LpIntegralFubini.integral_ae η ρ (fun a ↦ w a • K a) hwK raw hi he

end SHEStochastic.GlobalHeatRowInputIntegration
