module

public import SHEStochastic.FiniteScalarIto
public import SHEStochastic.GaussianMomentScaling
public import SHEStochastic.ConditionalCharacteristic
public import SHE.KolmogorovModification
public import SHE.HaarContinuousVersion
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.BrownianCoordinateVersions
open MeasureTheory ProbabilityTheory SHE Set
open scoped NNReal ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Coordinates F μ H ι)

def process (i : ι) (r : ℝ) (sample : Ω) : ℝ := P.W i (HaarUnitTimeMoments.clock H r) sample

theorem ordered_moment (hH : (H : ℝ) ≤ 1) (i : ι)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    (∫⁻ sample, ENNReal.ofReal (‖process P i s sample-process P i t sample‖^16) ∂μ) ≤
      ENNReal.ofReal (GaussianMomentScaling.moment 8 * |s-t|^2) := by
  have hc : HaarUnitTimeMoments.clock H s ≤ HaarUnitTimeMoments.clock H t := by
    change (HaarUnitTimeMoments.clock H s : ℝ) ≤ (HaarUnitTimeMoments.clock H t : ℝ)
    rw [HaarUnitTimeMoments.clock_coe H hs, HaarUnitTimeMoments.clock_coe H ht]
    exact mul_le_mul_of_nonneg_left hst H.coe_nonneg
  have hl := BrownianCoordinates.increment_law F μ H P.W P.law i
    (HaarUnitTimeMoments.clock H s) (HaarUnitTimeMoments.clock H t) hc
    (HaarUnitTimeMoments.clock_bound H t)
  have hv : ((HaarUnitTimeMoments.clock H t-HaarUnitTimeMoments.clock H s : ℝ≥0) : ℝ)^8 ≤ |s-t|^2 := by
    rw [NNReal.coe_sub hc, HaarUnitTimeMoments.clock_coe H ht, HaarUnitTimeMoments.clock_coe H hs,
      ← mul_sub, mul_pow, sq_abs]
    have hd0 : 0 ≤ t-s := sub_nonneg.mpr hst
    have hd1 : t-s ≤ 1 := by linarith [hs.1, ht.2]
    calc
      _ ≤ 1*(t-s)^8 := mul_le_mul_of_nonneg_right (pow_le_one₀ H.coe_nonneg hH) (pow_nonneg hd0 8)
      _ ≤ (t-s)^2 := by simpa only [one_mul] using (pow_le_pow_of_le_one hd0 hd1 (by decide : 2 ≤ 8))
      _ = (s-t)^2 := by ring
  calc
    _ = ENNReal.ofReal (((HaarUnitTimeMoments.clock H t-HaarUnitTimeMoments.clock H s : ℝ≥0) : ℝ)^8 *
        GaussianMomentScaling.moment 8) := by
      simpa only [process, norm_sub_rev] using GaussianMomentScaling.law_sixteenth hl
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hv (GaussianMomentScaling.moment_nonneg 8))

theorem increment_moment (hH : (H : ℝ) ≤ 1) (i : ι)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫⁻ sample, ENNReal.ofReal (‖process P i s sample-process P i t sample‖^16) ∂μ) ≤
      ENNReal.ofReal (GaussianMomentScaling.moment 8 * |s-t|^2) := by
  rcases le_total s t with hst | hts
  · exact ordered_moment P hH i hs ht hst
  · simpa only [norm_sub_rev, abs_sub_comm] using ordered_moment P hH i ht hs hts

def version (i : ι) (t : ℝ≥0) (sample : Ω) : ℝ :=
  KolmogorovModification.modification (process P i) (HaarContinuousVersion.normalizedTime H t) sample

theorem continuous (hH : 0 < H) (i : ι) (sample : Ω) : Continuous (fun t ↦ version P i t sample) :=
  (KolmogorovModification.continuousOn_modification (process P i) sample).comp_continuous
    (HaarContinuousVersion.continuous_normalizedTime H) (HaarContinuousVersion.normalizedTime_mem hH)

theorem version_ae (hH : 0 < H) (hH1 : (H : ℝ) ≤ 1) (i : ι) (t : ℝ≥0) :
    version P i t =ᵐ[μ] P.W i (min t H) := by
  have hh := KolmogorovModification.modification_ae μ (process P i)
    (fun r _ ↦ FiniteScalarIto.measurable_coordinate P i _) (GaussianMomentScaling.moment_nonneg 8)
    (fun s hs t ht ↦ increment_moment P hH1 i hs ht) (HaarContinuousVersion.normalizedTime_mem hH t)
  filter_upwards [hh] with sample hh
  change version P i t sample = P.W i (HaarUnitTimeMoments.clock H (HaarContinuousVersion.normalizedTime H t)) sample at hh
  rw [HaarContinuousVersion.clock_normalizedTime hH t] at hh
  exact hh

theorem predictable (hH : 0 < H) (hH1 : (H : ℝ) ≤ 1)
    (hn : NullCompleteFiltration.ContainsNullSets F μ) (i : ι) :
    StronglyMeasurable[F.predictable] (Function.uncurry (version P i)) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions F μ hn
  · intro t
    exact ⟨P.W i (min t H), ((P.adapted i _).mono (F.mono (min_le_left t H)) le_rfl).stronglyMeasurable,
      version_ae P hH hH1 i t⟩
  · exact continuous P hH i

/-- Finite-horizon Brownian coordinates already admit an adapted,
everywhere continuous family on a null-complete filtration. The SAME
coordinate classes are retained, including after Girsanov transport. -/
def family (hH : 0 < H) (hH1 : (H : ℝ) ≤ 1)
    (hn : NullCompleteFiltration.ContainsNullSets F μ) : FiniteScalarIto.Family F μ H ι where
  W := version P
  adapted i t := ((show IsStronglyPredictable F (version P i) from predictable P hH hH1 hn i).stronglyAdapted t).measurable
  continuous := continuous P hH
  law n a := by
    constructor
    · intro times ht
      apply ((P.law n a).1 times ht).congr
      filter_upwards [ae_all_iff.mpr (fun i : Fin n ↦ version_ae P hH hH1 (a i) (times i))] with sample hs
      apply PiLp.ext
      intro i
      simpa only [min_eq_left (ht i)] using hs i
    · intro s t hst ht
      have he : (fun sample ↦ WithLp.toLp 2 (fun i : Fin n ↦ version P (a i) t sample-version P (a i) s sample)) =ᵐ[μ]
          fun sample ↦ WithLp.toLp 2 (fun i : Fin n ↦ P.W (a i) t sample-P.W (a i) s sample) := by
        filter_upwards [ae_all_iff.mpr (fun i : Fin n ↦ version_ae P hH hH1 (a i) t),
          ae_all_iff.mpr (fun i : Fin n ↦ version_ae P hH hH1 (a i) s)] with sample hti hsi
        apply PiLp.ext
        intro i
        simpa only [min_eq_left ht, min_eq_left (hst.trans ht)] using congrArg₂ (· - ·) (hti i) (hsi i)
      have hh := ConditionalCharacteristic.indep_comap_congr (F s) he
        (by simpa only [BorelSpace.measurable_eq] using (P.law n a).2 s t hst ht)
      simpa only [BorelSpace.measurable_eq] using hh

end SHEStochastic.BrownianCoordinateVersions
