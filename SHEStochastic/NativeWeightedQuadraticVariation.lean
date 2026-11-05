module

public import SHEStochastic.NativeQuadraticFluctuation
public import SHEStochastic.NativeWeightedEnergy
public import SHEStochastic.PartitionIncrementL2
public import SHEStochastic.WeightedSquaresL2
public import SHEStochastic.BoundedPredictableDensity
public import SHEStochastic.L1Approximation
public import MathFin.Foundations.GirsanovPredictableTheta

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.NativeWeightedQuadraticVariation
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

def sum (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, w (unifPart H n i) ω *
    (J.integral (stop F μ H (unifPart H n (i + 1)) u) ω -
      J.integral (stop F μ H (unifPart H n i) u) ω) ^ 2

theorem stronglyMeasurable_sum (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w) (n : ℕ) :
    StronglyMeasurable (sum J u w n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact ((hw _).mono (F.le _)).mul
    (((Lp.stronglyMeasurable _).sub (Lp.stronglyMeasurable _)).pow 2)

/-- The exact fluctuation-plus-energy decomposition uses the same
original predictable row and the same chosen terminal integral. -/
theorem sum_eq (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sum (FiniteCylindricalIto.terminalIto P.toCoordinates e) u w n ω =
      NativeQuadraticFluctuation.fluctuation P e u w n ω + NativeWeightedEnergy.sum u w n ω := by
  rw [sum, NativeQuadraticFluctuation.fluctuation, NativeWeightedEnergy.sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [QuadraticBandError.error]
  ring

/-- Weighted quadratic variation for bounded predictable Hilbert rows,
under the full original filtration, proved without the Itô-formula box. -/
theorem bounded (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    TendstoInMeasure μ (sum (FiniteCylindricalIto.terminalIto P.toCoordinates e) u w)
      Filter.atTop (NativeWeightedEnergy.integral u w) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n ↦
    (stronglyMeasurable_sum _ u w hw n).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hf, he⟩ := MathFin.exists_subseq_tendsto_ae₂
    (NativeQuadraticFluctuation.tendstoInMeasure P e u M hu w hw B hB hwb)
    (NativeWeightedEnergy.tendstoInMeasure u w hw hc B hB hwb) ns hns.tendsto_atTop
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hf, he] with ω hfω heω
  simpa only [sum_eq, zero_add] using hfω.add heω

/-- The auxiliary L² increment array represents exactly the chosen
stopped-integral increments at every cell of the finite partition. -/
theorem sum_embedding_ae (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    (fun ω ↦ WeightedSquaresL2.value (fun i : Fin n ↦ w (unifPart H n i) ω)
      (PartitionIncrementL2.embedding J u n ω)) =ᵐ[μ] sum J u w n := by
  have hi : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      PartitionIncrementL2.increment J u n i ω =
        J.integral (stop F μ H (unifPart H n (i + 1)) u) ω -
          J.integral (stop F μ H (unifPart H n i) u) ω :=
    ae_all_iff.mpr (fun i ↦ Lp.coeFn_sub _ _)
  filter_upwards [PartitionIncrementL2.embedding_ae J u n, hi] with ω he hiω
  rw [he]
  apply Finset.sum_congr rfl
  intro i hi
  change w (unifPart H n i) ω * (PartitionIncrementL2.increment J u n i ω) ^ 2 = _
  rw [hiω i]

theorem integrable_sum (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) :
    Integrable (sum J u w n) μ :=
  (WeightedSquaresL2.integrable_value (PartitionIncrementL2.embedding J u n)
    (fun i ↦ w (unifPart H n i))
    (fun i ↦ ((hw _).mono (F.le _)).aestronglyMeasurable) B (fun i ↦ hwb _)).congr (sum_embedding_ae J u w n)

/-- The L¹ approximation error is uniform in the partition and in its
number of cells. No boundedness of either predictable row is needed. -/
theorem integral_sub_le (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u v : Process (E := C) F μ H)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) :
    (∫ ω, |sum J u w n ω - sum J v w n ω| ∂μ) ≤
      B * (‖u - v‖ * (‖u‖ + ‖v‖)) := by
  let A := PartitionIncrementL2.embedding J u n
  let D := PartitionIncrementL2.embedding J v n
  have he : (fun ω ↦ |sum J u w n ω - sum J v w n ω|) =ᵐ[μ]
      (fun ω ↦ |WeightedSquaresL2.value (fun i : Fin n ↦ w (unifPart H n i) ω) (A ω) -
        WeightedSquaresL2.value (fun i : Fin n ↦ w (unifPart H n i) ω) (D ω)|) := by
    filter_upwards [sum_embedding_ae J u w n, sum_embedding_ae J v w n] with ω hu hv
    rw [hu, hv]
  rw [integral_congr_ae he]
  refine (WeightedSquaresL2.integral_sub_le A D (fun i ↦ w (unifPart H n i))
    (fun i ↦ ((hw _).mono (F.le _)).aestronglyMeasurable) B hB (fun i ↦ hwb _)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hB
  apply mul_le_mul _ _ (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  · change ‖PartitionIncrementL2.embedding J u n - PartitionIncrementL2.embedding J v n‖ ≤ _
    rw [← PartitionIncrementL2.embedding_sub]
    exact PartitionIncrementL2.norm_embedding_le J hlocal (u - v) n
  · exact add_le_add (PartitionIncrementL2.norm_embedding_le J hlocal u n)
      (PartitionIncrementL2.norm_embedding_le J hlocal v n)

/-- For a bounded row, the stronger L¹ convergence follows from the
mean-square fluctuation estimate and the ordinary energy limit. -/
theorem tendsto_integral_abs_sub_bounded
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    Filter.Tendsto (fun n ↦ ∫ ω, |sum (FiniteCylindricalIto.terminalIto P.toCoordinates e) u w n ω -
      NativeWeightedEnergy.integral u w ω| ∂μ) Filter.atTop (𝓝 0) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hE := NativeWeightedEnergy.integrable u w hp B hwb
  have hb (n : ℕ) :
      (∫ ω, |sum J u w n ω - NativeWeightedEnergy.integral u w ω| ∂μ) ≤
        (∫ ω, |NativeQuadraticFluctuation.fluctuation P e u w n ω| ∂μ) +
          ∫ ω, |NativeWeightedEnergy.sum u w n ω - NativeWeightedEnergy.integral u w ω| ∂μ := by
    have hf := (NativeQuadraticFluctuation.memLp_fluctuation P e u M hu w hw B hB hwb n).integrable one_le_two
    have hs := NativeWeightedEnergy.integrable_sum u w hw B hB hwb n
    have hint : (∫ ω, |NativeQuadraticFluctuation.fluctuation P e u w n ω| ∂μ) +
        (∫ ω, |NativeWeightedEnergy.sum u w n ω - NativeWeightedEnergy.integral u w ω| ∂μ) =
        ∫ ω, |NativeQuadraticFluctuation.fluctuation P e u w n ω| +
          |(NativeWeightedEnergy.sum u w n - NativeWeightedEnergy.integral u w) ω| ∂μ := by
      simpa only [Pi.sub_apply] using (integral_add hf.abs (hs.sub hE).abs).symm
    rw [hint]
    apply integral_mono ((integrable_sum J u w hw B hwb n).sub hE).abs
      (hf.abs.add (hs.sub hE).abs)
    intro ω
    change |sum J u w n ω - NativeWeightedEnergy.integral u w ω| ≤ _
    rw [sum_eq]
    simpa only [add_sub_assoc, Pi.add_apply, Pi.sub_apply] using abs_add_le (NativeQuadraticFluctuation.fluctuation P e u w n ω)
      (NativeWeightedEnergy.sum u w n ω - NativeWeightedEnergy.integral u w ω)
  apply squeeze_zero (fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) hb
  simpa only [zero_add] using (NativeQuadraticFluctuation.tendsto_integral_abs P e u M hu w hw B hB hwb).add
    (NativeWeightedEnergy.tendsto_integral_abs_sub u w hw hc B hB hwb)

/-- Weighted quadratic variation for every original predictable L²
Hilbert row. Bounded simple density and a uniform L¹ comparison remove
the row bound; neither an Itô formula nor BDG is assumed. -/
theorem tendsto_integral_abs_sub
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    Filter.Tendsto (fun n ↦ ∫ ω, |sum (FiniteCylindricalIto.terminalIto P.toCoordinates e) u w n ω -
      NativeWeightedEnergy.integral u w ω| ∂μ) Filter.atTop (𝓝 0) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hlocal := FiniteCylindricalIto.pastLocality P e
  obtain ⟨v, hv, ht⟩ := BoundedPredictableDensity.exists_sequence e u
  have he : Filter.Tendsto (fun k ↦ (2 * B) * (‖u - v k‖ * (‖u‖ + ‖v k‖)))
      Filter.atTop (𝓝 0) := by
    have hd : Filter.Tendsto (fun k ↦ ‖u - v k‖) Filter.atTop (𝓝 0) := by
      simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp ht
    simpa only [zero_mul, mul_zero] using (hd.mul (tendsto_const_nhds.add ht.norm)).const_mul (2 * B)
  apply L1Approximation.tendsto_zero (fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) he
    (b := fun k n ↦ ∫ ω, |sum J (v k) w n ω - NativeWeightedEnergy.integral (v k) w ω| ∂μ)
  · intro k
    obtain ⟨M, hM⟩ := hv k
    exact tendsto_integral_abs_sub_bounded P e (v k) M hM w hw hp hc B hB hwb
  · intro k n
    have huI := integrable_sum J u w hw B hwb n
    have hvI := integrable_sum J (v k) w hw B hwb n
    have huE := NativeWeightedEnergy.integrable u w hp B hwb
    have hvE := NativeWeightedEnergy.integrable (v k) w hp B hwb
    have ht1 := L1Approximation.triangle huI hvI huE
    have ht2 := L1Approximation.triangle hvI hvE huE
    have h1 := integral_sub_le J hlocal u (v k) w hw B hB hwb n
    have h2 := NativeWeightedEnergy.integral_sub_le (v k) u w hp B hB hwb
    rw [norm_sub_rev (v k) u, add_comm ‖v k‖ ‖u‖] at h2
    linarith

theorem tendstoInMeasure (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry w))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 H))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    TendstoInMeasure μ (sum (FiniteCylindricalIto.terminalIto P.toCoordinates e) u w)
      Filter.atTop (NativeWeightedEnergy.integral u w) := by
  apply MathFin.ItoFormulaAdapted.tendstoInMeasure_of_tendsto_integral_abs
  · intro n
    exact (integrable_sum _ u w hw B hwb n).sub (NativeWeightedEnergy.integrable u w hp B hwb)
  · exact (NativeWeightedEnergy.integrable u w hp B hwb).aestronglyMeasurable
  · exact tendsto_integral_abs_sub P e u w hw hp hc B hB hwb

end SHEStochastic.NativeWeightedQuadraticVariation
