module

public import SHEStochastic.ContinuousStoppedMartingaleTests
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MartingaleCrossPairing
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

/-- Past multiplication can be unbounded when the actual product is
integrable. This is the ordinary conditional-expectation pullout. -/
theorem past_mul (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (s t : ℝ≥0) (hst : s ≤ t) (Z : Ω → ℝ) (hZ : StronglyMeasurable[F s] Z)
    (hprod : Integrable (fun sample ↦ Z sample * M t sample) μ) :
    (∫ sample, Z sample * M t sample ∂μ) = ∫ sample, Z sample * M s sample ∂μ := by
  have hp := condExp_mul_of_stronglyMeasurable_left hZ hprod (hM.integrable t)
  calc
    _ = ∫ sample, μ[fun sample ↦ Z sample * M t sample | F s] sample ∂μ :=
      (integral_condExp (F.le s)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hp, hM.condExp_ae_eq hst] with sample hp hm
      exact hp.trans (congrArg (fun v ↦ Z sample * v) hm)

/-- A joint cross-compensator determines pairing with each bounded
predictable Brownian cell. No martingale representation theorem is
used: this is derived from the two ordinary martingale identities. -/
theorem cell (M B A : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (hB : StronglyAdapted F B)
    (hCross : Martingale (fun r sample ↦ M r sample * B r sample - A r sample) F μ)
    (H : ℝ≥0) (hM2 : ∀ r, r ≤ H → MemLp (M r) 2 μ)
    (hB2 : ∀ r, r ≤ H → MemLp (B r) 2 μ)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[F s] Z) (K : ℝ) (hK : ∀ sample, ‖Z sample‖ ≤ K) :
    (∫ sample, M H sample * (Z sample * (B t sample-B s sample)) ∂μ) =
      ∫ sample, Z sample * (A t sample-A s sample) ∂μ := by
  have hs := hst.trans ht
  have hZm : AEStronglyMeasurable Z μ := (hZ.mono (F.le s)).aestronglyMeasurable
  have hi (r q : ℝ≥0) (hr : r ≤ H) (hq : q ≤ H) :
      Integrable (fun sample ↦ Z sample * (M r sample * B q sample)) μ :=
    ((hM2 r hr).integrable_mul (hB2 q hq)).bdd_mul hZm (Filter.Eventually.of_forall hK)
  have hAI (r : ℝ≥0) (hr : r ≤ H) : Integrable (A r) μ := by
    convert ((hM2 r hr).integrable_mul (hB2 r hr)).sub (hCross.integrable r) using 1
    funext sample
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hZA (r : ℝ≥0) (hr : r ≤ H) : Integrable (fun sample ↦ Z sample * A r sample) μ :=
    (hAI r hr).bdd_mul hZm (Filter.Eventually.of_forall hK)
  have hOne : (∫ sample, Z sample * (M H sample * B t sample) ∂μ) =
      ∫ sample, Z sample * (M t sample * B t sample) ∂μ := by
    have hm : StronglyMeasurable[F t] (fun sample ↦ Z sample * B t sample) :=
      (hZ.mono (F.mono hst)).mul (hB t)
    have hp : Integrable (fun sample ↦ (Z sample * B t sample) * M H sample) μ := by
      convert hi H t le_rfl ht using 1
      funext sample
      ring
    convert past_mul μ F M hM t H ht _ hm hp using 1 <;>
      apply integral_congr_ae <;> filter_upwards with sample <;> ring
  have hTwo : (∫ sample, Z sample * (M H sample * B s sample) ∂μ) =
      ∫ sample, Z sample * (M s sample * B s sample) ∂μ := by
    have hm : StronglyMeasurable[F s] (fun sample ↦ Z sample * B s sample) := hZ.mul (hB s)
    have hp : Integrable (fun sample ↦ (Z sample * B s sample) * M H sample) μ := by
      convert hi H s le_rfl hs using 1
      funext sample
      ring
    convert past_mul μ F M hM s H hs _ hm hp using 1 <;>
      apply integral_congr_ae <;> filter_upwards with sample <;> ring
  have hc := ContinuousStoppedMartingaleTests.weighted_increment μ F _ hCross s t hst Z hZ K hK
  have hc' : (∫ sample, Z sample * (M t sample * B t sample) ∂μ) -
      (∫ sample, Z sample * (M s sample * B s sample) ∂μ) =
      (∫ sample, Z sample * A t sample ∂μ) - ∫ sample, Z sample * A s sample ∂μ := by
    have he : (∫ sample, Z sample * ((M t sample * B t sample-A t sample) -
        (M s sample * B s sample-A s sample)) ∂μ) =
      ((∫ sample, Z sample * (M t sample * B t sample) ∂μ) - ∫ sample, Z sample * (M s sample * B s sample) ∂μ) -
      ((∫ sample, Z sample * A t sample ∂μ) - ∫ sample, Z sample * A s sample ∂μ) := by
      calc
        _ = ∫ sample, (Z sample * (M t sample * B t sample) - Z sample * (M s sample * B s sample)) -
            (Z sample * A t sample - Z sample * A s sample) ∂μ := by
          apply integral_congr_ae
          filter_upwards with sample
          ring
        _ = _ := by
          simpa only [Pi.sub_apply] using
            (integral_sub ((hi t t ht ht).sub (hi s s hs hs)) ((hZA t ht).sub (hZA s hs))).trans
              (congrArg₂ (· - ·) (integral_sub (hi t t ht ht) (hi s s hs hs))
                (integral_sub (hZA t ht) (hZA s hs)))
    rw [he] at hc
    linarith
  calc
    _ = (∫ sample, Z sample * (M H sample * B t sample) ∂μ) -
        ∫ sample, Z sample * (M H sample * B s sample) ∂μ := by
      rw [← integral_sub (hi H t le_rfl ht) (hi H s le_rfl hs)]
      apply integral_congr_ae
      filter_upwards with sample
      ring
    _ = _ := by
      rw [hOne, hTwo, hc', ← integral_sub (hZA t ht) (hZA s hs)]
      apply integral_congr_ae
      filter_upwards with sample
      ring

end SHEStochastic.MartingaleCrossPairing
