module

public import SHEStochastic.FiniteHorizonIntegratedHeat
public import SHEStochastic.UnboundedHeatTimeMoments
public import SHEStochastic.UnboundedFiniteHorizonInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalIncrementEnergy
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Set
open SublinearHeatIntegratedEnergy UnboundedHeatFamily
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

def rowCap (G : E → V) (C β : ℝ≥0) (R : ℝ) (H T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*SublinearHeatFiniteHorizon.constant (H:ℝ)^(1+(β:ℝ)))*stateFactor R β*
    ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/2)/((1-(β:ℝ))/2))

def timeCap (G : E → V) (C β : ℝ≥0) (R : ℝ) (H T δ : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.timeConstant (H:ℝ)^(1+(β:ℝ))*
    (δ:ℝ)^((1-(β:ℝ))/4))*stateFactor R β*ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/4)/((1-(β:ℝ))/4))+
    rowCap G C β R H δ

def spaceCap (G : E → V) (C β : ℝ≥0) (R : ℝ) (H T : ℝ≥0) (a b : HeatCircle) : ℝ≥0∞ :=
  ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.spaceConstant (H:ℝ)^(1+(β:ℝ))*
    (‖NativeHeatSpan.unitCenter a-NativeHeatSpan.unitCenter b‖^2)^((1-(β:ℝ))/4))*stateFactor R β*
    ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/4)/((1-(β:ℝ))/4))

include hG hβ1 in
/-- Added noise on (T,T+δ] is controlled on the actual original clock,
using the common finite horizon only in a deterministic heat constant. -/
theorem new_noise_bound (H T δ : ℝ≥0) (hS : T+δ≤H) (a : HeatCircle) {R : ℝ}
    (W : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
    (hW : ∀ᵐ s ∂timeMeasure H, ‖W s‖≤R) :
    (∫⁻ s in Ioc T (T+δ), rowEnergy G (W s) a (((T+δ:ℝ≥0):ℝ)-(s:ℝ)) ∂timeMeasure H)≤
      rowCap G C β R H δ := by
  have hm := DeterministicItoShift.time_translation H T δ hS
  have hemb : MeasurableEmbedding (fun s : ℝ≥0 ↦ T+s) :=
    (continuous_const.add continuous_id).measurableEmbedding (by intro s r h; exact add_left_cancel h)
  have hshift : ∀ᵐ s ∂timeMeasure δ, ‖W (T+s)‖≤R := hm.quasiMeasurePreserving.ae (ae_restrict_of_ae hW)
  have hδH : (δ:ℝ)≤H := by exact_mod_cast (le_add_of_nonneg_left (show (0:ℝ≥0)≤T from zero_le)).trans hS
  have hb := SublinearHeatFiniteHorizon.row_bound_until hG hβ1 δ δ le_rfl (H:ℝ) hδH a (fun s ↦ W (T+s)) hshift
  calc
    _ = ∫⁻ s, rowEnergy G (W (T+s)) a (((T+δ:ℝ≥0):ℝ)-((T+s:ℝ≥0):ℝ)) ∂timeMeasure δ :=
      (hm.lintegral_comp_emb hemb _).symm
    _ = ∫⁻ s, rowEnergy G (W (T+s)) a ((δ:ℝ)-(s:ℝ)) ∂timeMeasure δ := by
      apply lintegral_congr
      intro s
      congr 1
      push_cast
      ring
    _ ≤ _ := hb

/-- Global temporal energy estimate, reusing the exact local split. -/
theorem time_integrated (H T δ : ℝ≥0) (hS : T+δ≤H) (a : HeatCircle) {R : ℝ} (ω : Ω)
    (hW : ∀ᵐ s ∂timeMeasure H, ‖U (s,ω)‖≤R) :
    (∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 (T+δ) a (s,ω)-
      family F U hU hG hβ hβ1 T a (s,ω)‖^2) ∂timeMeasure H)≤timeCap G C β R H T δ := by
  rw [UnboundedHeatTimeMoments.integrated_split]
  exact add_le_add (FiniteHorizonIntegratedHeat.time_bound hG hβ1 T H
    ((le_add_of_nonneg_right (show (0:ℝ≥0)≤δ from zero_le)).trans hS) a δ (fun s ↦ U (s,ω)) hW)
    (new_noise_bound hG hβ1 H T δ hS a (fun s ↦ U (s,ω)) hW)

/-- Global spatial energy estimate for the same native Hilbert row. -/
theorem space_integrated (H T : ℝ≥0) (hTH : T≤H) (a b : HeatCircle) {R : ℝ} (ω : Ω)
    (hW : ∀ᵐ s ∂timeMeasure H, ‖U (s,ω)‖≤R) :
    (∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a (s,ω)-
      family F U hU hG hβ hβ1 T b (s,ω)‖^2) ∂timeMeasure H)≤ spaceCap G C β R H T a b := by
  exact (lintegral_congr fun s ↦ spatial_energy F U hU hG hβ hβ1 T a b (s,ω)).trans_le
    (FiniteHorizonIntegratedHeat.space_bound hG hβ1 T H hTH a b (fun s ↦ U (s,ω)) hW)

theorem time_bracket (μ : Measure Ω) [IsProbabilityMeasure μ] (H T δ : ℝ≥0) (hS : T+δ≤H)
    (a : HeatCircle) {R : ℝ} (hW : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 (T+δ) a (s,ω)-
      family F U hU hG hβ hβ1 T a (s,ω)‖^2) ∂timeMeasure H)≤timeCap G C β R H T δ := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hW
  exact (Measure.ae_ae_of_ae_prod hs).mono fun ω hω ↦ time_integrated F U hU hG hβ hβ1 H T δ hS a ω hω

theorem space_bracket (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0) (hTH : T≤H)
    (a b : HeatCircle) {R : ℝ} (hW : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a (s,ω)-
      family F U hU hG hβ hβ1 T b (s,ω)‖^2) ∂timeMeasure H)≤ spaceCap G C β R H T a b := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hW
  exact (Measure.ae_ae_of_ae_prod hs).mono fun ω hω ↦ space_integrated F U hU hG hβ hβ1 H T hTH a b ω hω

end SHEStochastic.UnboundedGlobalIncrementEnergy
