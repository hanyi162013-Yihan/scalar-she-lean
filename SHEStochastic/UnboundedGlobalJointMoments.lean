module

public import SHEStochastic.UnboundedGlobalIncrementCaps
public import SHEStochastic.GlobalHeatParameter
public import SHEStochastic.IncrementEnergyTriangle

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.UnboundedGlobalJointMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open UnboundedHeatFamily HeatParameterCover HeatParameterCoordinates UnboundedHeatIncrementCaps
open UnboundedGlobalIncrementEnergy
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

theorem ordered_bracket (μ : Measure Ω) [IsProbabilityMeasure μ] (H T δ : ℝ≥0)
    (hS : T+δ≤H) (a b : HeatCircle) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 (T+δ) a (s,ω)-
      family F U hU hG hβ hβ1 T b (s,ω)‖^2) ∂timeMeasure H)≤2*(timeCap G C β R H T δ+spaceCap G C β R H T a b) := by
  have hTH : T≤H := (le_add_of_nonneg_right (show (0:ℝ≥0)≤δ from zero_le)).trans hS
  filter_upwards [time_bracket F U hU hG hβ hβ1 μ H T δ hS a hbound,
    space_bracket F U hU hG hβ hβ1 μ H T hTH a b hbound] with ω ht hs
  have hm : Measurable (fun s : ℝ≥0 ↦ ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a (s,ω)-
      family F U hU hG hβ hβ1 T b (s,ω)‖^2)) :=
    (((((UnboundedHeatFamily.stronglyMeasurable F U hU hG hβ hβ1 T a).sub
      (UnboundedHeatFamily.stronglyMeasurable F U hU hG hβ hβ1 T b)).mono
      (predictable_le_product F)).norm.pow 2).measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
  exact (IncrementEnergyTriangle.integrated (timeMeasure H)
    (fun s ↦ family F U hU hG hβ hβ1 (T+δ) a (s,ω))
    (fun s ↦ family F U hU hG hβ hβ1 T a (s,ω))
    (fun s ↦ family F U hU hG hβ hβ1 T b (s,ω)) hm).trans (mul_le_mul_right (add_le_add ht hs) 2)

def jointConstant (G : E → V) (C β : ℝ≥0) (R : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  2*(UnboundedGlobalIncrementCaps.timeConstant G C β R H*ENNReal.ofReal ((H:ℝ)^exponent β)+
    UnboundedGlobalIncrementCaps.spaceConstant G C β R H)

theorem ordered_parameter_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) (hpq : GlobalHeatParameter.time H q≤GlobalHeatParameter.time H p) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (GlobalHeatParameter.time H p) (center p) (s,ω)-
        family F U hU hG hβ hβ1 (GlobalHeatParameter.time H q) (center q) (s,ω)‖^2) ∂timeMeasure H)≤
      jointConstant G C β R H*ENNReal.ofReal (dist p q^exponent β) := by
  let δ := GlobalHeatParameter.time H p-GlobalHeatParameter.time H q
  have he : GlobalHeatParameter.time H q+δ=GlobalHeatParameter.time H p := add_tsub_cancel_of_le hpq
  have hδH : δ≤H := tsub_le_self.trans (GlobalHeatParameter.time_le_horizon H p)
  have hd : (δ:ℝ)≤(H:ℝ)*dist p q := by
    have hh := (GlobalHeatParameter.time_lipschitz H).dist_le_mul p q
    simp only [NNReal.dist_eq, abs_of_nonneg (show 0≤(GlobalHeatParameter.time H p:ℝ)-
      (GlobalHeatParameter.time H q:ℝ) from sub_nonneg.mpr (by exact_mod_cast hpq))] at hh
    simpa only [δ, NNReal.coe_sub hpq] using hh
  have hq := exponent_pos hβ1
  have htime := UnboundedGlobalIncrementCaps.time_bound G C β hβ1 R H
    (GlobalHeatParameter.time H q) δ (GlobalHeatParameter.time_le_horizon H q) hδH
  have hpow : (δ:ℝ)^exponent β≤(H:ℝ)^exponent β*dist p q^exponent β := by
    exact (Real.rpow_le_rpow δ.property hd hq.le).trans_eq (Real.mul_rpow H.property dist_nonneg)
  have ht0 := htime.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hpow) _)
  have hprod : ENNReal.ofReal ((H:ℝ)^exponent β*dist p q^exponent β)=
      ENNReal.ofReal ((H:ℝ)^exponent β)*ENNReal.ofReal (dist p q^exponent β) := by
    convert! ENNReal.ofReal_mul (Real.rpow_nonneg H.property (exponent β)) (q := dist p q^exponent β) using 1
  have ht := ht0.trans_eq (congrArg
    (fun z : ℝ≥0∞ ↦ UnboundedGlobalIncrementCaps.timeConstant G C β R H*z) hprod)
  have hspace := UnboundedGlobalIncrementCaps.space_bound G C β hβ1 R H
    (GlobalHeatParameter.time H q) (GlobalHeatParameter.time_le_horizon H q) (center p) (center q)
  have hnorm1 : ‖NativeHeatSpan.unitCenter (center p)-NativeHeatSpan.unitCenter (center q)‖≤1 :=
    (AddCircle.norm_le_half_period (1:ℝ) one_ne_zero).trans (by norm_num)
  have hnorm : ‖NativeHeatSpan.unitCenter (center p)-NativeHeatSpan.unitCenter (center q)‖^(2*exponent β)≤dist p q^exponent β :=
    (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hnorm1 hq.le (by linarith)).trans
      (Real.rpow_le_rpow (norm_nonneg _) (spatial_distance_le p q) hq.le)
  have hs := hspace.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hnorm) _)
  have hb := ordered_bracket F U hU hG hβ hβ1 μ H (GlobalHeatParameter.time H q) δ
    (he ▸ GlobalHeatParameter.time_le_horizon H p) (center p) (center q) hbound
  rw [he] at hb
  exact hb.mono fun ω hω ↦ hω.trans ((mul_le_mul_right (add_le_add ht hs) 2).trans_eq (by dsimp [jointConstant]; ring))

theorem family_bracket (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (GlobalHeatParameter.time H p) (center p) (s,ω)-
        family F U hU hG hβ hβ1 (GlobalHeatParameter.time H q) (center q) (s,ω)‖^2) ∂timeMeasure H)≤
      jointConstant G C β R H*ENNReal.ofReal (dist p q^exponent β) := by
  rcases le_total (GlobalHeatParameter.time H q) (GlobalHeatParameter.time H p) with hpq | hqp
  · exact ordered_parameter_bound F U hU hG hβ hβ1 μ H p q hpq hbound
  · simpa only [norm_sub_rev, dist_comm] using ordered_parameter_bound F U hU hG hβ hβ1 μ H q p hqp hbound

def parameterInput (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R) (p : Parameter) :
    Process (E := Lp V 2 (haarAddCircle (T := 2*Real.pi))) F μ H :=
  UnboundedFiniteHorizonInput.input F U hU hG hβ hβ1 μ H (GlobalHeatParameter.time H p)
    (GlobalHeatParameter.time_le_horizon H p) (center p) hbound

theorem input_bracket (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖(parameterInput F U hU hG hβ hβ1 μ H hbound p-
      parameterInput F U hU hG hβ hβ1 μ H hbound q) (s,ω)‖^2) ∂timeMeasure H)≤
      jointConstant G C β R H*ENNReal.ofReal (dist p q^exponent β) := by
  let vp := parameterInput F U hU hG hβ hβ1 μ H hbound p
  let vq := parameterInput F U hU hG hβ hβ1 μ H hbound q
  have he : vp-vq=ᵐ[energyMeasure μ H] fun z ↦
      family F U hU hG hβ hβ1 (GlobalHeatParameter.time H p) (center p) z-
        family F U hU hG hβ hβ1 (GlobalHeatParameter.time H q) (center q) z := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub vp vq),
      UnboundedFiniteHorizonInput.input_ae F U hU hG hβ hβ1 μ H (GlobalHeatParameter.time H p)
        (GlobalHeatParameter.time_le_horizon H p) (center p) hbound,
      UnboundedFiniteHorizonInput.input_ae F U hU hG hβ hβ1 μ H (GlobalHeatParameter.time H q)
        (GlobalHeatParameter.time_le_horizon H q) (center q) hbound] with z hs hp hq
    simp only [Pi.sub_apply] at hs
    exact hs.trans (congrArg₂ (fun v w ↦ v-w) hp hq)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs, family_bracket F U hU hG hβ hβ1 μ H p q hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun s hx ↦ congrArg (fun v ↦ ENNReal.ofReal (‖v‖^2)) hx)).trans_le hb

theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖≤R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2*Real.pi)))) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (parameterInput F U hU hG hβ hβ1 μ H hbound p) ω-
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (parameterInput F U hU hG hβ hβ1 μ H hbound q) ω‖^(2*2^k)) ∂μ)≤
      ((NativeScalarBDG.constant k:ℝ≥0∞)*jointConstant G C β R H^(2^k))*edist p q^(exponent β*(2^k:ℕ)) := by
  have hb := NativeScalarBDG.difference_moment_of_bracket_bound P e k _ _
    (input_bracket F U hU hG hβ hβ1 μ H p q hbound)
  refine hb.trans_eq ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg (exponent_pos hβ1).le,
    mul_pow, ← ENNReal.rpow_mul_natCast, edist_dist]
  ring

theorem jointConstant_finite (G : E → V) (C β : ℝ≥0) (R : ℝ) (H : ℝ≥0) : jointConstant G C β R H<⊤ := by
  obtain ⟨ht,hs⟩ := UnboundedGlobalIncrementCaps.constants_finite G C β R H
  dsimp [jointConstant]
  finiteness

end SHEStochastic.UnboundedGlobalJointMoments
