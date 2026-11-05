module

public import SHEStochastic.UnboundedHeatIncrementCaps
public import SHEStochastic.HeatParameterCoordinates
public import SHEStochastic.IncrementEnergyTriangle

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.UnboundedHeatJointMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.NativeHeatSpan AddCircle
open UnboundedHeatFamily HeatParameterCover HeatParameterCoordinates UnboundedHeatIncrementCaps
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

theorem family_ordered_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T δ : ℝ≥0)
    (hS : T + δ ≤ H) (hT : (T : ℝ) ≤ 1) (hδ : (δ : ℝ) ≤ 1) (a b : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (T + δ) a (s, ω) -
        family F U hU hG hβ hβ1 T b (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
      2 * (UnboundedHeatTimeMoments.energyCap G C β R T δ +
        UnboundedHeatSpatialMoments.energyCap G C β R T a b) := by
  have hTH : T ≤ H := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from zero_le)).trans hS
  filter_upwards [UnboundedHeatTimeMoments.family_bracket_bound F U hU hG hβ hβ1
    μ H T δ hS hT hδ a hbound,
    UnboundedHeatSpatialMoments.family_bracket_bound F U hU hG hβ hβ1 μ H T hTH hT a b hbound]
    with ω ht hs
  have hm : Measurable (fun s : ℝ≥0 ↦ ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 T a (s, ω) - family F U hU hG hβ hβ1 T b (s, ω)‖ ^ 2)) :=
    (((((UnboundedHeatFamily.stronglyMeasurable F U hU hG hβ hβ1 T a).sub
      (UnboundedHeatFamily.stronglyMeasurable F U hU hG hβ hβ1 T b)).mono
      (predictable_le_product F)).norm.pow 2).measurable.comp
        (measurable_id.prodMk measurable_const)).ennreal_ofReal
  exact (IncrementEnergyTriangle.integrated (timeMeasure H)
    (fun s ↦ family F U hU hG hβ hβ1 (T + δ) a (s, ω))
    (fun s ↦ family F U hU hG hβ hβ1 T a (s, ω))
    (fun s ↦ family F U hU hG hβ hβ1 T b (s, ω)) hm).trans
      (mul_le_mul_right (add_le_add ht hs) 2)

def jointConstant (G : E → V) (C β : ℝ≥0) (R : ℝ) : ℝ≥0∞ :=
  2 * (timeConstant G C β R + spatialConstant G C β R)

theorem ordered_parameter_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) (hpq : time H q ≤ time H p) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (time H p) (center p) (s, ω) -
        family F U hU hG hβ hβ1 (time H q) (center q) (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
      jointConstant G C β R * ENNReal.ofReal (dist p q ^ exponent β) := by
  let δ := time H p - time H q
  have he : time H q + δ = time H p := add_tsub_cancel_of_le hpq
  have hδ1 : (δ : ℝ) ≤ 1 := by
    exact_mod_cast (tsub_le_self.trans (show time H p ≤ (1 : ℝ≥0) from time_le_one H p))
  have hδd : (δ : ℝ) ≤ dist p q := by
    have hd := (time_lipschitz H).dist_le_mul p q
    simp only [NNReal.coe_one, one_mul, NNReal.dist_eq, abs_of_nonneg (show
      0 ≤ (time H p : ℝ) - (time H q : ℝ) from sub_nonneg.mpr (by exact_mod_cast hpq))] at hd
    simpa only [δ, NNReal.coe_sub hpq] using hd
  have hq := exponent_pos hβ1
  have htime := UnboundedHeatIncrementCaps.time_bound G C β hβ1 R (time H q) δ (time_le_one H q) hδ1
  have hspace := UnboundedHeatIncrementCaps.spatial_bound G C β hβ1 R (time H q) (time_le_one H q) (center p) (center q)
  have hnorm1 : ‖unitCenter (center p) - unitCenter (center q)‖ ≤ 1 :=
    (AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero).trans (by norm_num)
  have hnorm : ‖unitCenter (center p) - unitCenter (center q)‖ ^ (2 * exponent β) ≤
      dist p q ^ exponent β :=
    (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hnorm1 hq.le (by linarith)).trans
      (Real.rpow_le_rpow (norm_nonneg _) (spatial_distance_le p q) hq.le)
  have hcap : 2 * (UnboundedHeatTimeMoments.energyCap G C β R (time H q) δ +
      UnboundedHeatSpatialMoments.energyCap G C β R (time H q) (center p) (center q)) ≤
      jointConstant G C β R * ENNReal.ofReal (dist p q ^ exponent β) := by
    have ht := htime.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow δ.property hδd hq.le)) _)
    have hs := hspace.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hnorm) _)
    exact (mul_le_mul_right (add_le_add ht hs) 2).trans_eq (by dsimp [jointConstant]; ring)
  have hb := family_ordered_bound F U hU hG hβ hβ1 μ H (time H q) δ
    (he ▸ time_le_horizon H p) (time_le_one H q) hδ1 (center p) (center q) hbound
  rw [he] at hb
  exact hb.mono fun _ h ↦ h.trans hcap

theorem family_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (time H p) (center p) (s, ω) -
        family F U hU hG hβ hβ1 (time H q) (center q) (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
      jointConstant G C β R * ENNReal.ofReal (dist p q ^ exponent β) := by
  rcases le_total (time H q) (time H p) with hpq | hqp
  · exact ordered_parameter_bound F U hU hG hβ hβ1 μ H p q hpq hbound
  · have hb := ordered_parameter_bound F U hU hG hβ hβ1 μ H q p hqp hbound
    simpa only [norm_sub_rev, dist_comm] using hb

def parameterInput (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {R : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R) (p : Parameter) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  input F U hU hG hβ hβ1 μ H (time H p) (time_le_horizon H p) (time_le_one H p) (center p) hbound

theorem input_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖(parameterInput F U hU hG hβ hβ1 μ H hbound p -
        parameterInput F U hU hG hβ hβ1 μ H hbound q) (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
      jointConstant G C β R * ENNReal.ofReal (dist p q ^ exponent β) := by
  let vp := parameterInput F U hU hG hβ hβ1 μ H hbound p
  let vq := parameterInput F U hU hG hβ hβ1 μ H hbound q
  have he : vp - vq =ᵐ[energyMeasure μ H] fun z ↦
      family F U hU hG hβ hβ1 (time H p) (center p) z -
        family F U hU hG hβ hβ1 (time H q) (center q) z := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub vp vq),
      input_ae F U hU hG hβ hβ1 μ H (time H p) (time_le_horizon H p) (time_le_one H p) (center p) hbound,
      input_ae F U hU hG hβ hβ1 μ H (time H q) (time_le_horizon H q) (time_le_one H q) (center q) hbound]
      with z hs hp hq
    simp only [Pi.sub_apply] at hs
    exact hs.trans (congrArg₂ (fun v w ↦ v - w) hp hq)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs,
    family_bracket_bound F U hU hG hβ hβ1 μ H p q hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun _ hx ↦ congrArg (fun v ↦ ENNReal.ofReal (‖v‖ ^ 2)) hx)).trans_le hb

/-- A single two-dimensional moment estimate, with a finite constant
and arbitrary dyadic order, for the actual native stochastic integral. -/
theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (p q : Parameter) {R : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H, ‖U z‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (parameterInput F U hU hG hβ hβ1 μ H hbound p) ω -
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (parameterInput F U hU hG hβ hβ1 μ H hbound q) ω‖ ^ (2 * 2 ^ k)) ∂μ) ≤
      ((NativeScalarBDG.constant k : ℝ≥0∞) * jointConstant G C β R ^ (2 ^ k)) *
        edist p q ^ (exponent β * (2 ^ k : ℕ)) := by
  have hb := NativeScalarBDG.difference_moment_of_bracket_bound P e k _ _
    (input_bracket_bound F U hU hG hβ hβ1 μ H p q hbound)
  refine hb.trans_eq ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg dist_nonneg (exponent_pos hβ1).le,
    mul_pow, ← ENNReal.rpow_mul_natCast, edist_dist]
  ring

theorem jointConstant_finite (G : E → V) (C β : ℝ≥0) (R : ℝ) :
    jointConstant G C β R < ⊤ := by
  obtain ⟨ht, hs⟩ := constants_finite G C β R
  dsimp [jointConstant]
  finiteness

end SHEStochastic.UnboundedHeatJointMoments
