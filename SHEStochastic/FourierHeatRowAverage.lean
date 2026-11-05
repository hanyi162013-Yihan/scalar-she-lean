module

public import SHEStochastic.NativeFourierHeatCoordinate
public import SHEStochastic.HeatRowSpatialAveraging

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.FourierHeatRowAverage
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle Filter
open UnboundedHeatFamily NativeFourierHeatCoordinate
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

def row (a : ℂ →L[ℝ] ℝ) (n : ℤ) : ℝ≥0 × Ω → Lp V 2 (haarAddCircle (T := 2 * Real.pi)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HolderStateRows.row U hU hG hβ hβ1.le (fun _ ↦ weight a n)

theorem stronglyMeasurable (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    StronglyMeasurable[F.predictable] (row F U hU hG hβ hβ1 a n) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HolderStateRows.stronglyMeasurable U hU hG hβ hβ1.le (fun _ ↦ weight a n)
    ((weight a n).continuous.measurable.comp measurable_snd)

theorem coefficient_energy (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) :
    ENNReal.ofReal (‖HolderCoefficientIntegrability.coefficient hβ hβ1.le hG u‖ ^ 2) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2) *
        (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by
  have hb := HolderWeightedEnergy.bound hG hβ1.le u (fun _ ↦ 1) aemeasurable_const 1 1
    (Eventually.of_forall fun _ ↦ le_rfl) (by simp)
  simp only [one_mul, ENNReal.one_rpow] at hb
  rw [← HolderWeightedEnergy.state_mass]
  exact (lintegral_congr_ae ((HolderCoefficientIntegrability.coefficient_ae hβ hβ1.le hG u).mono
    fun _ hx ↦ congrArg (fun v : V ↦ ENNReal.ofReal (‖v‖ ^ 2)) hx)).trans_le hb

theorem energy_bound (a : ℂ →L[ℝ] ℝ) (n : ℤ) (p : ℝ≥0 × Ω) :
    ENNReal.ofReal (‖row F U hU hG hβ hβ1 a n p‖ ^ 2) ≤
      ENNReal.ofReal (‖a‖ ^ 2) *
        (ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2) *
          (1 + ENNReal.ofReal (‖U p‖ ^ 2) ^ (β : ℝ))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hr := HolderStateRows.row_operator U hU hG hβ hβ1.le (fun _ ↦ weight a n) p
  change row F U hU hG hβ hβ1 a n p = _ at hr
  have hn : ‖row F U hU hG hβ hβ1 a n p‖ ≤
      ‖a‖ * ‖HolderCoefficientIntegrability.coefficient hβ hβ1.le hG (U p)‖ := by
    rw [hr]
    exact (ContinuousKernelLpAction.norm_bound haarAddCircle _ _).trans
      (mul_le_mul_of_nonneg_right (weight_norm_bound a n) (norm_nonneg _))
  calc
    _ ≤ ENNReal.ofReal ((‖a‖ * ‖HolderCoefficientIntegrability.coefficient hβ hβ1.le hG (U p)‖) ^ 2) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hn 2)
    _ = ENNReal.ofReal (‖a‖ ^ 2) *
        ENNReal.ofReal (‖HolderCoefficientIntegrability.coefficient hβ hβ1.le hG (U p)‖ ^ 2) := by
      rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ _ := mul_le_mul_right (coefficient_energy hG hβ hβ1 (U p)) _

theorem memLp (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    @MemLp _ _ F.predictable _ _ (row F U hU hG hβ hβ1 a n) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  have hp := stronglyMeasurable F U hU hG hβ hβ1 a n
  have hm := hp.mono (predictable_le_product F)
  let K := ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2) *
    SublinearHeatIntegratedEnergy.stateFactor R β
  have he : ∀ᵐ p ∂energyMeasure μ H, ENNReal.ofReal (‖row F U hU hG hβ hβ1 a n p‖ ^ 2) ≤ K := by
    filter_upwards [hbound] with p hp
    exact (energy_bound F U hU hG hβ hβ1 a n p).trans (by
      dsimp [K]
      rw [mul_assoc]
      exact mul_le_mul_right (mul_le_mul_right (SublinearHeatIntegratedEnergy.state_factor_le (U p) hp) _) _)
  have hi : (∫⁻ p, ENNReal.ofReal (‖row F U hU hG hβ hβ1 a n p‖ ^ 2) ∂energyMeasure μ H) < ⊤ := by
    refine (lintegral_mono_ae he).trans_lt ?_
    rw [lintegral_const]
    dsimp [K, SublinearHeatIntegratedEnergy.stateFactor]
    finiteness
  have hmem : MemLp (row F U hU hG hβ hβ1 a n) 2 (energyMeasure μ H) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    refine ⟨(hm.norm.pow 2).aestronglyMeasurable, ?_⟩
    change (∫⁻ p, ‖‖row F U hU hG hβ hβ1 a n p‖ ^ 2‖ₑ ∂energyMeasure μ H) < ⊤
    exact (lintegral_congr fun _ ↦ Real.enorm_eq_ofReal (sq_nonneg _)).trans_lt hi
  exact (le_of_eq (eLpNorm_trim (predictable_le_product F) hp)).trans_lt hmem

def input (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  (memLp F U hU hG hβ hβ1 μ H a n hbound).toLp _

theorem input_ae_trim (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    input F U hU hG hβ hβ1 μ H a n hbound =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      row F U hU hG hβ hβ1 a n :=
  (memLp F U hU hG hβ hβ1 μ H a n hbound).coeFn_toLp

/-- The exact Fourier average of an unbounded-coefficient noise row is
its unsmoothed Fourier row times the physical heat eigenvalue, with the
original strict causal time cutoff. -/
theorem family_average (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    (∫ x : HeatCircle, weight a n x • family F U hU hG hβ hβ1 T x p ∂haarAddCircle) =
      if p.1 < T then Real.exp (-((T : ℝ) - (p.1 : ℝ)) * (n : ℝ) ^ 2) •
        row F U hU hG hβ hβ1 a n p else 0 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  by_cases hp : p.1 < T
  · rw [if_pos hp]
    simp_rw [HeatRowSpatialAveraging.row_operator F U hU hG hβ hβ1]
    change _ = _ • HolderStateRows.row U hU hG hβ hβ1.le (fun _ ↦ weight a n) p
    rw [HolderStateRows.row_operator U hU hG hβ hβ1.le (fun _ ↦ weight a n) p]
    let L := ContinuousKernelLpAction.operator haarAddCircle
      (HolderCoefficientIntegrability.coefficient hβ hβ1.le hG (U p))
    let r : ℝ := (T : ℝ) - (p.1 : ℝ)
    have hr : 0 < r := sub_pos.mpr hp
    have hc : Continuous (fun x : HeatCircle ↦ weight a n x • RealCausalHeatKernel.value x r) :=
      (weight a n).continuous.smul (RealCausalHeatKernel.continuous_center hr)
    have hi : Integrable (fun x : HeatCircle ↦ weight a n x • RealCausalHeatKernel.value x r) haarAddCircle :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change (∫ x : HeatCircle, weight a n x • L (RealCausalHeatKernel.value x r) ∂haarAddCircle) =
      Real.exp (-r * (n : ℝ) ^ 2) • L (weight a n)
    calc
      _ = ∫ x : HeatCircle, L (weight a n x • RealCausalHeatKernel.value x r) ∂haarAddCircle :=
        integral_congr_ae (Eventually.of_forall fun x ↦ (L.map_smul _ _).symm)
      _ = L (∫ x : HeatCircle, weight a n x • RealCausalHeatKernel.value x r ∂haarAddCircle) :=
        L.integral_comp_comm hi
      _ = L (Real.exp (-r * (n : ℝ) ^ 2) • weight a n) := congrArg L (kernel_average a n hr)
      _ = _ := L.map_smul _ _
  · rw [if_neg hp]
    have hz (x : HeatCircle) : family F U hU hG hβ hβ1 T x p = 0 :=
      family_zero_after F U hU hG hβ hβ1 T x p (le_of_not_gt hp)
    simp only [hz, smul_zero, integral_zero]

end SHEStochastic.FourierHeatRowAverage
