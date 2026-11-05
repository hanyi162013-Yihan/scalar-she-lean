module

public import SHEStochastic.UnboundedHeatFamily
public import SHE.DeterministicItoShiftMeasure
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.UnboundedHeatTimeMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Set
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

/-- The temporal difference splits exactly into the common past-noise
increment and the newly added noise interval. -/
theorem energy_split (T δ : ℝ≥0) (a : HeatCircle) (p : ℝ≥0 × Ω) :
    ENNReal.ofReal (‖family F U hU hG hβ hβ1 (T + δ) a p - family F U hU hG hβ hβ1 T a p‖ ^ 2) =
      SublinearHeatIntegratedEnergy.timeEnergy G (U p) a δ ((T : ℝ) - (p.1 : ℝ)) +
        if T ≤ p.1 then SublinearHeatIntegratedEnergy.rowEnergy G (U p) a
          (((T + δ : ℝ≥0) : ℝ) - (p.1 : ℝ)) else 0 := by
  rw [difference_energy]
  by_cases hpre : p.1 < T
  · have hr : 0 < (T : ℝ) - (p.1 : ℝ) := sub_pos.mpr (by exact_mod_cast hpre)
    have he : ((T + δ : ℝ≥0) : ℝ) - (p.1 : ℝ) = (T : ℝ) - (p.1 : ℝ) + δ := by
      push_cast
      ring
    rw [SublinearHeatIntegratedEnergy.timeEnergy, dite_eq_left hr, if_neg (not_le_of_gt hpre), add_zero, he]
    apply lintegral_congr
    intro x
    apply congrArg ENNReal.ofReal
    apply congrArg (fun z : ℝ ↦ z * ‖G (U p x)‖ ^ 2)
    convert RealCausalHeatKernel.difference_square
      (add_pos_of_pos_of_nonneg hr δ.property) hr a a x using 1 <;> rfl
  · have hst : T ≤ p.1 := le_of_not_gt hpre
    have hr : (T : ℝ) - (p.1 : ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hst)
    rw [SublinearHeatIntegratedEnergy.timeEnergy, dite_eq_right (not_lt_of_ge hr),
      if_pos hst, zero_add, RealCausalHeatKernel.nonpos hr]
    simp only [ContinuousMap.zero_apply, sub_zero]
    by_cases hs : 0 < ((T + δ : ℝ≥0) : ℝ) - (p.1 : ℝ)
    · rw [SublinearHeatIntegratedEnergy.rowEnergy, dite_eq_left hs]
      apply lintegral_congr
      intro x
      rw [RealCausalHeatKernel.square hs a x]
    · simp only [SublinearHeatIntegratedEnergy.rowEnergy, dite_eq_right hs,
        RealCausalHeatKernel.nonpos (le_of_not_gt hs), ContinuousMap.zero_apply,
        zero_pow (by norm_num : 2 ≠ 0), zero_mul, ENNReal.ofReal_zero, lintegral_zero]

include hG hβ1 in
/-- The added noise uses only the original clock restricted to (T,T+δ].
The existing deterministic time-translation theorem reduces its energy
to the base heat-row bound on a horizon of length δ. -/
theorem new_noise_bound (H T δ : ℝ≥0) (hS : T + δ ≤ H) (hδ : (δ : ℝ) ≤ 1)
    (a : HeatCircle) {R : ℝ}
    (W : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hW : ∀ᵐ s ∂timeMeasure H, ‖W s‖ ≤ R) :
    (∫⁻ s in Ioc T (T + δ), SublinearHeatIntegratedEnergy.rowEnergy G (W s) a
      (((T + δ : ℝ≥0) : ℝ) - (s : ℝ)) ∂timeMeasure H) ≤ energyCap G C β R δ := by
  have hm := DeterministicItoShift.time_translation H T δ hS
  have hemb : MeasurableEmbedding (fun s : ℝ≥0 ↦ T + s) :=
    (continuous_const.add continuous_id).measurableEmbedding (by intro s r h; exact add_left_cancel h)
  have hshift : ∀ᵐ s ∂timeMeasure δ, ‖W (T + s)‖ ≤ R :=
    hm.quasiMeasurePreserving.ae (ae_restrict_of_ae hW)
  have hb := SublinearHeatIntegratedEnergy.row_bound hG hβ1 δ δ le_rfl hδ a (fun s ↦ W (T + s)) hshift
  change _ ≤ energyCap G C β R δ at hb
  calc
    _ = ∫⁻ s, SublinearHeatIntegratedEnergy.rowEnergy G (W (T + s)) a
        (((T + δ : ℝ≥0) : ℝ) - ((T + s : ℝ≥0) : ℝ)) ∂timeMeasure δ :=
      (hm.lintegral_comp_emb hemb _).symm
    _ = ∫⁻ s, SublinearHeatIntegratedEnergy.rowEnergy G (W (T + s)) a ((δ : ℝ) - (s : ℝ)) ∂timeMeasure δ := by
      apply lintegral_congr
      intro s
      congr 1
      push_cast
      ring
    _ ≤ _ := hb

def energyCap (G : E → V) (C β : ℝ≥0) (R : ℝ) (T δ : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
    SublinearHeatTimeIncrement.smallTimeConstant ^ (1 + (β : ℝ)) *
      (δ : ℝ) ^ ((1 - (β : ℝ)) / 4)) * SublinearHeatIntegratedEnergy.stateFactor R β *
        ENNReal.ofReal ((T : ℝ) ^ ((1 - (β : ℝ)) / 4) / ((1 - (β : ℝ)) / 4)) +
    UnboundedHeatFamily.energyCap G C β R δ

/-- Exact integrated common-past/new-noise split, with no unit-time
restriction. Both local and global estimates reuse this identity. -/
theorem integrated_split (H T δ : ℝ≥0) (a : HeatCircle) (ω : Ω) :
    (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (T+δ) a (s,ω)-family F U hU hG hβ hβ1 T a (s,ω)‖^2) ∂timeMeasure H)=
      (∫⁻ s, SublinearHeatIntegratedEnergy.timeEnergy G (U (s,ω)) a δ ((T:ℝ)-(s:ℝ)) ∂timeMeasure H)+
      ∫⁻ s in Ioc T (T+δ), SublinearHeatIntegratedEnergy.rowEnergy G (U (s,ω)) a
        (((T+δ:ℝ≥0):ℝ)-(s:ℝ)) ∂timeMeasure H := by
  let tail : ℝ≥0 → ℝ≥0∞ := (Ioc T (T + δ)).indicator (fun s ↦
    ENNReal.ofReal (‖family F U hU hG hβ hβ1 (T + δ) a (s, ω)‖ ^ 2))
  have hm : Measurable tail :=
    ((((UnboundedHeatFamily.stronglyMeasurable F U hU hG hβ hβ1 (T + δ) a).mono
      (predictable_le_product F)).norm.pow 2).measurable.comp (measurable_id.prodMk measurable_const))
      |>.ennreal_ofReal.indicator measurableSet_Ioc
  have he : (fun s ↦ ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (T + δ) a (s, ω) -
        family F U hU hG hβ hβ1 T a (s, ω)‖ ^ 2)) =ᵐ[timeMeasure H]
      fun s ↦ SublinearHeatIntegratedEnergy.timeEnergy G (U (s, ω)) a δ
        ((T : ℝ) - (s : ℝ)) + tail s := by
    filter_upwards [(timeMeasure H).ae_ne T] with s hne
    rw [energy_split]
    congr 1
    by_cases hts : T < s
    · rw [if_pos hts.le]
      by_cases hs : s ≤ T + δ
      · rw [show tail s = ENNReal.ofReal
            (‖family F U hU hG hβ hβ1 (T + δ) a (s, ω)‖ ^ 2) from
            Set.indicator_of_mem (show s ∈ Ioc T (T + δ) from ⟨hts, hs⟩) _, energy]
      · rw [show tail s = 0 from Set.indicator_of_notMem (by exact fun h ↦ hs h.2) _]
        exact dif_neg (not_lt_of_ge (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hs))))
    · have hlt : s < T := lt_of_le_of_ne (le_of_not_gt hts) hne
      rw [if_neg (not_le_of_gt hlt)]
      exact (Set.indicator_of_notMem (by exact fun h ↦ (not_lt_of_ge hlt.le) h.1) _).symm
  rw [lintegral_congr_ae he, lintegral_add_right _ hm]
  congr 1
  rw [show (∫⁻ s, tail s ∂timeMeasure H)=
      ∫⁻ s in Ioc T (T+δ), ENNReal.ofReal (‖family F U hU hG hβ hβ1 (T+δ) a (s,ω)‖^2) ∂timeMeasure H from
    lintegral_indicator measurableSet_Ioc _]
  exact lintegral_congr fun s ↦ energy F U hU hG hβ hβ1 (T+δ) a (s,ω)

theorem family_integrated_bound (H T δ : ℝ≥0) (hS : T + δ ≤ H)
    (hT : (T : ℝ) ≤ 1) (hδ : (δ : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ} (ω : Ω)
    (hW : ∀ᵐ s ∂timeMeasure H, ‖U (s, ω)‖ ≤ R) :
    (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (T + δ) a (s, ω) -
        family F U hU hG hβ hβ1 T a (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
          energyCap G C β R T δ := by
  rw [integrated_split]
  exact add_le_add (SublinearHeatIntegratedEnergy.time_bound hG hβ1 T H
    ((le_add_of_nonneg_right (show (0:ℝ≥0)≤δ from zero_le)).trans hS) hT a δ hδ
    (fun s ↦ U (s,ω)) hW) (new_noise_bound hG hβ1 H T δ hS hδ a (fun s ↦ U (s,ω)) hW)

theorem family_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T δ : ℝ≥0)
    (hS : T + δ ≤ H) (hT : (T : ℝ) ≤ 1) (hδ : (δ : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 (T + δ) a (s, ω) -
        family F U hU hG hβ hβ1 T a (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
          energyCap G C β R T δ := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hbound
  exact (Measure.ae_ae_of_ae_prod hs).mono fun ω hω ↦
    family_integrated_bound F U hU hG hβ hβ1 H T δ hS hT hδ a ω hω

theorem input_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T δ : ℝ≥0)
    (hS : T + δ ≤ H) (hTH : T ≤ H) (hS1 : ((T + δ : ℝ≥0) : ℝ) ≤ 1) (hT : (T : ℝ) ≤ 1)
    (a : HeatCircle) {R : ℝ} (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖(input F U hU hG hβ hβ1 μ H (T + δ) hS hS1 a hbound -
        input F U hU hG hβ hβ1 μ H T hTH hT a hbound) (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
          energyCap G C β R T δ := by
  let va := input F U hU hG hβ hβ1 μ H (T + δ) hS hS1 a hbound
  let vb := input F U hU hG hβ hβ1 μ H T hTH hT a hbound
  have he : va - vb =ᵐ[energyMeasure μ H] fun p ↦
      family F U hU hG hβ hβ1 (T + δ) a p - family F U hU hG hβ hβ1 T a p := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub va vb),
      input_ae F U hU hG hβ hβ1 μ H (T + δ) hS hS1 a hbound,
      input_ae F U hU hG hβ hβ1 μ H T hTH hT a hbound] with p hs ha hb
    simp only [Pi.sub_apply] at hs
    exact hs.trans (by rw [ha, hb])
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  have hδ : (δ : ℝ) ≤ 1 := (le_add_of_nonneg_left T.property).trans (by exact_mod_cast hS1)
  filter_upwards [Measure.ae_ae_of_ae_prod hs,
    family_bracket_bound F U hU hG hβ hβ1 μ H T δ hS hT hδ a hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun _ hx ↦ congrArg (fun v ↦ ENNReal.ofReal (‖v‖ ^ 2)) hx)).trans_le hb

/-- Temporal differences of actual native stochastic observations have
all dyadic moments; both old noise and the new interval are accounted for. -/
theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H T δ : ℝ≥0)
    (hS : T + δ ≤ H) (hTH : T ≤ H) (hS1 : ((T + δ : ℝ≥0) : ℝ) ≤ 1) (hT : (T : ℝ) ≤ 1)
    (a : HeatCircle) {R : ℝ} (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (input F U hU hG hβ hβ1 μ H (T + δ) hS hS1 a hbound) ω -
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (input F U hU hG hβ hβ1 μ H T hTH hT a hbound) ω‖ ^ (2 * 2 ^ k)) ∂μ) ≤
      (NativeScalarBDG.constant k : ℝ≥0∞) * energyCap G C β R T δ ^ (2 ^ k) :=
  NativeScalarBDG.difference_moment_of_bracket_bound P e k _ _
    (input_bracket_bound F U hU hG hβ hβ1 μ H T δ hS hTH hS1 hT a hbound)

end SHEStochastic.UnboundedHeatTimeMoments
