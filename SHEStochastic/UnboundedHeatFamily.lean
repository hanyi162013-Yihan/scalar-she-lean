module

public import SHEStochastic.HolderStateRows
public import SHEStochastic.RealCausalHeatKernel
public import SHEStochastic.SublinearHeatIntegratedEnergy
public import SHEStochastic.NativeScalarBDG
public import SHE.PredictableClock
public import SHE.StoppedInputParameter

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.UnboundedHeatFamily
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
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

def kernelFamily (T : ℝ≥0) (a : HeatCircle) (p : ℝ≥0 × Ω) : C(HeatCircle, ℝ) :=
  RealCausalHeatKernel.value a ((T : ℝ) - (p.1 : ℝ))

def family (T : ℝ≥0) (a : HeatCircle) : ℝ≥0 × Ω → Lp V 2 (haarAddCircle (T := 2 * Real.pi)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HolderStateRows.row U hU hG hβ hβ1.le (kernelFamily T a)

theorem state_congr (W : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hW : StronglyMeasurable[F.predictable] W) (T : ℝ≥0) (a : HeatCircle)
    (p : ℝ≥0 × Ω) (hp : U p = W p) :
    family F U hU hG hβ hβ1 T a p = family F W hW hG hβ hβ1 T a p := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HolderStateRows.row_state_congr U hU hG hβ hβ1.le (kernelFamily T a) W hW p hp

theorem stronglyMeasurable (T : ℝ≥0) (a : HeatCircle) :
    StronglyMeasurable[F.predictable] (family F U hU hG hβ hβ1 T a) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HolderStateRows.stronglyMeasurable U hU hG hβ hβ1.le (kernelFamily T a)
    (RealCausalHeatKernel.measurable_family a _ (measurable_const.sub (PredictableClock.real_time_measurable F)))

theorem energy (T : ℝ≥0) (a : HeatCircle) (p : ℝ≥0 × Ω) :
    ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a p‖ ^ 2) =
      SublinearHeatIntegratedEnergy.rowEnergy G (U p) a ((T : ℝ) - (p.1 : ℝ)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change ENNReal.ofReal (‖HolderStateRows.row U hU hG hβ hβ1.le (kernelFamily T a) p‖ ^ 2) = _
  rw [HolderStateRows.energy]
  by_cases hr : 0 < (T : ℝ) - (p.1 : ℝ)
  · simp only [SublinearHeatIntegratedEnergy.rowEnergy, dite_eq_left hr]
    apply lintegral_congr
    intro x
    rw [kernelFamily, RealCausalHeatKernel.square hr a x]
  · simp only [SublinearHeatIntegratedEnergy.rowEnergy, dite_eq_right hr, kernelFamily,
      RealCausalHeatKernel.nonpos (le_of_not_gt hr), ContinuousMap.zero_apply,
      zero_pow (by norm_num : 2 ≠ 0), zero_mul, ENNReal.ofReal_zero, lintegral_zero]

theorem family_zero_after (T : ℝ≥0) (a : HeatCircle) (p : ℝ≥0 × Ω)
    (ht : (T : ℝ) ≤ p.1) : family F U hU hG hβ hβ1 T a p = 0 := by
  have hz : ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a p‖ ^ 2) = 0 := by
    rw [energy]
    simp only [SublinearHeatIntegratedEnergy.rowEnergy,
      dite_eq_right (not_lt.mpr (sub_nonpos.mpr ht))]
  have hh := ENNReal.ofReal_eq_zero.mp hz
  apply norm_eq_zero.mp
  exact le_antisymm (by nlinarith [norm_nonneg (family F U hU hG hβ hβ1 T a p)]) (norm_nonneg _)

theorem difference_energy (T S : ℝ≥0) (a b : HeatCircle) (p : ℝ≥0 × Ω) :
    ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a p - family F U hU hG hβ hβ1 S b p‖ ^ 2) =
      ∫⁻ x, ENNReal.ofReal
        ((RealCausalHeatKernel.value a ((T : ℝ) - (p.1 : ℝ)) x -
          RealCausalHeatKernel.value b ((S : ℝ) - (p.1 : ℝ)) x) ^ 2 * ‖G (U p x)‖ ^ 2) ∂haarAddCircle := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HolderStateRows.difference_energy U hU hG hβ hβ1.le (kernelFamily T a) (kernelFamily S b) p

theorem spatial_energy (T : ℝ≥0) (a b : HeatCircle) (p : ℝ≥0 × Ω) :
    ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a p - family F U hU hG hβ hβ1 T b p‖ ^ 2) =
      SublinearHeatIntegratedEnergy.spatialEnergy G (U p) a b ((T : ℝ) - (p.1 : ℝ)) := by
  rw [difference_energy]
  by_cases hr : 0 < (T : ℝ) - (p.1 : ℝ)
  · simp only [SublinearHeatIntegratedEnergy.spatialEnergy, dite_eq_left hr]
    apply lintegral_congr
    intro x
    rw [RealCausalHeatKernel.difference_square hr hr a b x]
  · simp only [SublinearHeatIntegratedEnergy.spatialEnergy, dite_eq_right hr,
      RealCausalHeatKernel.nonpos (le_of_not_gt hr), ContinuousMap.zero_apply, sub_self,
      zero_pow (by norm_num : 2 ≠ 0), zero_mul, ENNReal.ofReal_zero, lintegral_zero]

def energyCap (G : E → V) (C β : ℝ≥0) (R : ℝ) (T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * ScaledHeatTraceEnvelope.constant 1 2 ^ (1 + (β : ℝ))) *
    SublinearHeatIntegratedEnergy.stateFactor R β *
      ENNReal.ofReal ((T : ℝ) ^ ((1 - (β : ℝ)) / 2) / ((1 - (β : ℝ)) / 2))

/-- The actual predictable Hilbert rows have a deterministic bracket
bound after L² localization, on the original integration horizon H. -/
theorem bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
      energyCap G C β R T := by
  have hs : ∀ᵐ p ∂μ.prod (timeMeasure H), ‖U (p.2, p.1)‖ ≤ R :=
    (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hbound
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  have hh := SublinearHeatIntegratedEnergy.row_bound hG hβ1 T H hTH hT a
    (fun s ↦ U (s, ω)) hω
  change _ ≤ energyCap G C β R T at hh
  exact (lintegral_congr fun s ↦ energy F U hU hG hβ hβ1 T a (s, ω)).trans_le hh

theorem memLp (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    @MemLp _ _ F.predictable _ _ (family F U hU hG hβ hβ1 T a) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hp := stronglyMeasurable F U hU hG hβ hβ1 T a
  have hm := hp.mono (predictable_le_product F)
  have he : (∫⁻ p, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a p‖ ^ 2) ∂energyMeasure μ H) ≤
      energyCap G C β R T := by
    calc
      _ = ∫⁻ ω, ∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a (s, ω)‖ ^ 2) ∂timeMeasure H ∂μ :=
        lintegral_prod_symm _ (hm.norm.pow 2).measurable.ennreal_ofReal.aemeasurable
      _ ≤ ∫⁻ _ : Ω, energyCap G C β R T ∂μ :=
        lintegral_mono_ae (bracket_bound F U hU hG hβ hβ1 μ H T hTH hT a hbound)
      _ = _ := by simp
  have hf : (∫⁻ p, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a p‖ ^ 2) ∂energyMeasure μ H) < ⊤ :=
    he.trans_lt (by dsimp [energyCap, SublinearHeatIntegratedEnergy.stateFactor]; finiteness)
  have hmem : MemLp (family F U hU hG hβ hβ1 T a) 2 (energyMeasure μ H) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    refine ⟨(hm.norm.pow 2).aestronglyMeasurable, ?_⟩
    change (∫⁻ p, ‖‖family F U hU hG hβ hβ1 T a p‖ ^ 2‖ₑ ∂energyMeasure μ H) < ⊤
    exact (lintegral_congr fun _ ↦ Real.enorm_eq_ofReal (sq_nonneg _)).trans_lt hf
  exact (le_of_eq (eLpNorm_trim (predictable_le_product F) hp)).trans_lt hmem

/-- Actual original-horizon stochastic input for a sublinear coefficient.
It is a member of the predictable L² space, built from physical energy. -/
def input (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  (memLp F U hU hG hβ hβ1 μ H T hTH hT a hbound).toLp _

theorem input_ae (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    input F U hU hG hβ hβ1 μ H T hTH hT a hbound =ᵐ[energyMeasure μ H]
      family F U hU hG hβ hβ1 T a :=
  ae_eq_of_ae_eq_trim (memLp F U hU hG hβ hβ1 μ H T hTH hT a hbound).coeFn_toLp

theorem input_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖input F U hU hG hβ hβ1 μ H T hTH hT a hbound (s, ω)‖ ^ 2) ∂timeMeasure H) ≤ energyCap G C β R T := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (input_ae F U hU hG hβ hβ1 μ H T hTH hT a hbound)
  filter_upwards [Measure.ae_ae_of_ae_prod hs,
    bracket_bound F U hU hG hβ hβ1 μ H T hTH hT a hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun _ hx ↦ congrArg (fun v ↦ ENNReal.ofReal (‖v‖ ^ 2)) hx)).trans_le hb

/-- The causal input already ends at its observation time T. Hence
the continuous stopped-integral version at T represents the terminal
convolution used in the heat moment and continuity estimates. -/
theorem input_stop (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    StoppedItoInputs.stop F μ H T (input F U hU hG hβ hβ1 μ H T hTH hT a hbound) =
      input F U hU hG hβ hβ1 μ H T hTH hT a hbound := by
  apply Lp.ext
  filter_upwards [StoppedInputParameter.stop_ae_trim F μ H
    (input F U hU hG hβ hβ1 μ H T hTH hT a hbound) T,
    (memLp F U hU hG hβ hβ1 μ H T hTH hT a hbound).coeFn_toLp] with p hs hi
  rw [hs]
  by_cases ht : (p.1 : ℝ) < T
  · exact Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) T from ht) _
  · rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) T from ht)]
    exact (hi.trans (family_zero_after F U hU hG hβ hβ1 T a p (le_of_not_gt ht))).symm

/-- Every dyadic stochastic moment follows for the constructed original
input from native BDG. There is no additional stochastic estimate premise. -/
theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (input F U hU hG hβ hβ1 μ H T hTH hT a hbound) ω‖ ^ (2 * 2 ^ k)) ∂μ) ≤
      (NativeScalarBDG.constant k : ℝ≥0∞) * energyCap G C β R T ^ (2 ^ k) := by
  exact NativeScalarBDG.moment_of_bracket_bound P e k _
    (input_bracket_bound F U hU hG hβ hβ1 μ H T hTH hT a hbound)

end SHEStochastic.UnboundedHeatFamily
