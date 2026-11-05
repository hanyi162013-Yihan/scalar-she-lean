module

public import SHEStochastic.PredictableLeftSteps
public import SHE.PredictableProcessLimit
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.PredictableEnvelopeMultiplier
open MeasureTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

theorem path_bound (w : ℝ≥0 → Ω → ℝ) (D : Ω → ℝ)
    (hb : ∀ᵐ ω ∂μ, ∀ t, |w t ω| ≤ D ω) :
    ∀ᵐ p ∂energyMeasure μ H, |w p.1 p.2| ≤ D p.2 := by
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := timeMeasure H) (ν := μ)).ae hb]
    with p hp
  exact hp p.1

/-- A random L² envelope suffices for multiplying a bounded predictable
row. The envelope itself need not be predictable. -/
theorem memLp (u : Process (E := C) F μ H) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (w : ℝ≥0 × Ω → ℝ) (hw : StronglyMeasurable[F.predictable] w)
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hb : ∀ᵐ p ∂energyMeasure μ H, |w p| ≤ D p.2) :
    @MemLp _ _ F.predictable _ _ (fun p ↦ w p • u p) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hf := hw.smul (Lp.stronglyMeasurable u)
  have ha : MemLp (fun p ↦ w p • u p) 2 (energyMeasure μ H) := by
    apply (hD.comp_snd (timeMeasure H)).of_le_mul (c := M)
      (hf.mono (predictable_le_product F)).aestronglyMeasurable
    filter_upwards [ae_of_ae_trim (predictable_le_product F) hu, hb] with p hp hbω
    change ‖w p • u p‖ ≤ M * ‖D p.2‖
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ |w p| * M := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ ≤ |D p.2| * M := mul_le_mul_of_nonneg_right (hbω.trans (le_abs_self _)) hM
      _ = _ := mul_comm _ _
  exact (le_of_eq (eLpNorm_trim (predictable_le_product F) hf)).trans_lt ha

def process (u : Process (E := C) F μ H) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (w : ℝ≥0 × Ω → ℝ) (hw : StronglyMeasurable[F.predictable] w)
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hb : ∀ᵐ p ∂energyMeasure μ H, |w p| ≤ D p.2) :
    Process (E := C) F μ H := (memLp u M hM hu w hw D hD hb).toLp (fun p ↦ w p • u p)

theorem process_ae (u : Process (E := C) F μ H) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (w : ℝ≥0 × Ω → ℝ) (hw : StronglyMeasurable[F.predictable] w)
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hb : ∀ᵐ p ∂energyMeasure μ H, |w p| ≤ D p.2) :
    process u M hM hu w hw D hD hb =ᵐ[energyMeasure μ H] (fun p ↦ w p • u p) :=
  ae_eq_of_ae_eq_trim (memLp u M hM hu w hw D hD hb).coeFn_toLp

/-- Dominated convergence of random-envelope multipliers takes place
in the original predictable L² space, although domination is proved
in the physical time/sample product space. -/
theorem tendsto (u : Process (E := C) F μ H) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M)
    (w : ℕ → ℝ≥0 × Ω → ℝ) (hw : ∀ n, StronglyMeasurable[F.predictable] (w n))
    (g : ℝ≥0 × Ω → ℝ) (hg : StronglyMeasurable[F.predictable] g)
    (D : Ω → ℝ) (hD : MemLp D 2 μ)
    (hb : ∀ n, ∀ᵐ p ∂energyMeasure μ H, |w n p| ≤ D p.2)
    (hgb : ∀ᵐ p ∂energyMeasure μ H, |g p| ≤ D p.2)
    (hlim : ∀ᵐ p ∂energyMeasure μ H, Tendsto (fun n ↦ w n p) atTop (𝓝 (g p))) :
    Tendsto (fun n ↦ process u M hM hu (w n) (hw n) D hD (hb n)) atTop
      (𝓝 (process u M hM hu g hg D hD hgb)) := by
  let V (n : ℕ) := process u M hM hu (w n) (hw n) D hD (hb n)
  let U := process u M hM hu g hg D hD hgb
  have hn (n : ℕ) : ∀ᵐ p ∂energyMeasure μ H, ‖V n p‖ ≤ M * |D p.2| := by
    filter_upwards [process_ae u M hM hu (w n) (hw n) D hD (hb n),
      ae_of_ae_trim (predictable_le_product F) hu, hb n] with p hp hq hbω
    change V n p = _ at hp
    rw [hp, norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg (w n p), abs_nonneg (D p.2), hbω,
      le_abs_self (D p.2), norm_nonneg (u p)]
  have hU : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ M * |D p.2| := by
    filter_upwards [process_ae u M hM hu g hg D hD hgb,
      ae_of_ae_trim (predictable_le_product F) hu, hgb] with p hp hq hbω
    change U p = _ at hp
    rw [hp, norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg (g p), abs_nonneg (D p.2), hbω,
      le_abs_self (D p.2), norm_nonneg (u p)]
  have ha : ∀ᵐ p ∂energyMeasure μ H, Tendsto (fun n ↦ V n p) atTop (𝓝 (U p)) := by
    filter_upwards [ae_all_iff.mpr (fun n ↦ process_ae u M hM hu (w n) (hw n) D hD (hb n)),
      process_ae u M hM hu g hg D hD hgb, hlim] with p hp hq ht
    change ∀ n, V n p = w n p • u p at hp
    change U p = g p • u p at hq
    have hf : (fun n ↦ V n p) = (fun n ↦ w n p • u p) := funext hp
    rw [hf, hq]
    exact ht.smul_const (u p)
  have hE := tendsto_integral_filter_of_dominated_convergence (μ := energyMeasure μ H)
    (fun p ↦ 4 * M ^ 2 * D p.2 ^ 2)
    (F := fun n p ↦ ‖V n p - U p‖ ^ 2) (f := fun _ ↦ (0 : ℝ))
    (Eventually.of_forall fun n ↦ (((Lp.stronglyMeasurable (V n)).sub (Lp.stronglyMeasurable U)).mono
      (predictable_le_product F)).norm.pow 2 |>.aestronglyMeasurable)
    (Eventually.of_forall fun n ↦ by
      filter_upwards [hn n, hU] with p hp hq
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hh := (norm_sub_le (V n p) (U p)).trans (add_le_add hp hq)
      nlinarith [norm_nonneg (V n p - U p), sq_abs (D p.2)])
    ((hD.comp_snd (timeMeasure H)).integrable_sq.const_mul (4 * M ^ 2))
    (ha.mono fun p hp ↦ by
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        (hp.sub (tendsto_const_nhds (x := U p))).norm.pow 2)
  have he : Tendsto (fun n ↦ ∫ p, ‖V n p - U p‖ ^ 2 ∂energyMeasure μ H) atTop (𝓝 0) := by
    simpa only [integral_zero] using hE
  have hs := he.sqrt
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [PredictableProcessLimit.product_energy_eq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    dist_eq_norm] using hs

end SHEStochastic.PredictableEnvelopeMultiplier
