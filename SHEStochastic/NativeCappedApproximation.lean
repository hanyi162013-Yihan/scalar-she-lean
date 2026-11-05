module

public import SHEStochastic.NativeEnergy
public import SHEStochastic.HilbertSimpleEnergyCap
public import SHEStochastic.HilbertSimpleTimeCut
public import Mathlib.Topology.Sequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeCappedApproximation
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open FilteredSimplePartition

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "emb" => HilbertSimpleInputs.embedding F μ H

theorem simple_energy_ae (V : HilbertSimpleInputs.bounded (E := C) F H) :
    NativeEnergy.energy (emb V) =ᵐ[μ] (fun ω ↦ ∫ r, ‖V.val r ω‖ ^ 2 ∂νt) :=
  NativeEnergy.energy_ae_of_ae _ _ (HilbertSimpleInputs.embedding_ae F μ H V)

theorem sub_simple_energy_ae (V U : HilbertSimpleInputs.bounded (E := C) F H) :
    NativeEnergy.energy (emb V - emb U) =ᵐ[μ]
      (fun ω ↦ ∫ r, ‖V.val r ω - U.val r ω‖ ^ 2 ∂νt) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply NativeEnergy.energy_ae_of_ae _ (fun p ↦ V.val p.1 p.2 - U.val p.1 p.2)
  filter_upwards [Lp.coeFn_sub (emb V) (emb U), HilbertSimpleInputs.embedding_ae F μ H V,
    HilbertSimpleInputs.embedding_ae F μ H U] with p hs hV hU
  change (emb V - emb U) p = _
  rw [hs, Pi.sub_apply, hV, hU]
  rfl

/-- Predictable energy clipping costs no more in native L2 than the L1
energy error of the original approximation. -/
theorem loss_bound (V : HilbertSimpleInputs.bounded (E := C) F H)
    (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : marshalPart F H V.val N = H)
    (u : Lp C 2 νin) (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    ‖emb V - emb (HilbertSimpleEnergyCap.cap V K N)‖ ^ 2 ≤
      ∫ ω, |NativeEnergy.energy (emb V) ω - NativeEnergy.energy u ω| ∂μ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [← NativeEnergy.mean_eq]
  apply integral_mono_ae (NativeEnergy.integrable _)
    ((NativeEnergy.integrable _).sub (NativeEnergy.integrable _)).abs
  filter_upwards [simple_energy_ae V,
    sub_simple_energy_ae V (HilbertSimpleEnergyCap.cap V K N), hu] with ω hV hd huω
  simp only [Pi.sub_apply]
  rw [hd, hV]
  exact (HilbertSimpleEnergyCap.cap_loss_le V K hK N hN ω).trans
    (SimpleEnergyCapAlgebra.excess_le_error huω)

/-- Bounded-energy native inputs have simple approximations with the
same pathwise energy cap. No future-dependent truncation is used. -/
theorem exists_sequence {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    ∃ V : ℕ → HilbertSimpleInputs.bounded (E := C) F H,
      (∀ n ω, (∫ r, ‖(V n).val r ω‖ ^ 2 ∂νt) ≤ K) ∧
      Filter.Tendsto (fun n ↦ emb (V n)) Filter.atTop (𝓝 u) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((HilbertSimpleInputs.embedding_dense (F := F) (μ := μ) (H := H) e) u)
  choose V hV using hv
  have horig : Filter.Tendsto (fun n ↦ emb (V n)) Filter.atTop (𝓝 u) := by
    simpa only [hV] using hlim
  let N (n : ℕ) := (marshalEndpoints F H (V n).val).card - 1
  have hN (n : ℕ) : marshalPart F H (V n).val (N n) = H :=
    marshalPart_card_sub_one F H (V n).val (V n).property
  let U (n : ℕ) := HilbertSimpleEnergyCap.cap (V n) K (N n)
  refine ⟨U, fun n ω ↦ ?_, ?_⟩
  · exact (HilbertSimpleEnergyCap.cap_energy_le (V n) K hK (N n) (hN n) ω).trans
      (min_le_right _ _)
  · have hsq : Filter.Tendsto (fun n ↦ ‖emb (V n) - emb (U n)‖ ^ 2)
        Filter.atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ sq_nonneg _) (fun n ↦ loss_bound (V n) K hK (N n) (hN n) u hu)
        (NativeEnergy.tendsto_energy_sub horig)
    have hn : Filter.Tendsto (fun n ↦ ‖emb (V n) - emb (U n)‖)
        Filter.atTop (𝓝 0) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
        hsq.sqrt
    have hdiff : Filter.Tendsto (fun n ↦ emb (V n) - emb (U n))
        Filter.atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
    have hf := horig.sub hdiff
    simpa only [sub_sub_cancel, sub_zero] using hf

theorem cut_energy_le (s : ℝ≥0) (hsH : s ≤ H)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (ω : Ω) :
    (∫ r, ‖(HilbertSimpleTimeCut.cut s hsH V).val r ω‖ ^ 2 ∂νt) ≤
      ∫ r, ‖V.val r ω‖ ^ 2 ∂νt := by
  apply integral_mono (HilbertSimplePartition.path_memLp _ ω).norm.integrable_sq
    (HilbertSimplePartition.path_memLp _ ω).norm.integrable_sq
  intro r
  change ‖(HilbertSimpleTimeCut.cut s hsH V).val r ω‖ ^ 2 ≤ ‖V.val r ω‖ ^ 2
  rw [HilbertSimpleTimeCut.cut_apply]
  by_cases hr : r ∈ Set.Ioc s H
  · rw [Set.indicator_of_mem hr]
  · rw [Set.indicator_of_notMem hr, norm_zero, zero_pow two_ne_zero]
    exact sq_nonneg _

/-- The same capped approximation may start after any fixed past time.
The deterministic cut preserves the cap and contracts approximation error. -/
theorem exists_sequence_after {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ C)
    (s : ℝ≥0) (hsH : s ≤ H) (u : Lp C 2 νin)
    (hus : ∀ᵐ p ∂νin, p.1 ≤ s → u p = 0) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    ∃ V : ℕ → HilbertSimpleInputs.bounded (E := C) F H,
      (∀ n p, p ∈ (V n).val.value.support → s ≤ p.1) ∧
      (∀ n ω, (∫ r, ‖(V n).val r ω‖ ^ 2 ∂νt) ≤ K) ∧
      Filter.Tendsto (fun n ↦ emb (V n)) Filter.atTop (𝓝 u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨V, hcap, hlim⟩ := exists_sequence e u K hK hu
  let U (n : ℕ) := HilbertSimpleTimeCut.cut s hsH (V n)
  refine ⟨U, fun n ↦ HilbertSimpleTimeCut.cut_starts_after s hsH (V n),
    fun n ω ↦ (cut_energy_le s hsH (V n) ω).trans (hcap n ω), ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ HilbertSimpleTimeCut.embedding_cut_sub_le s hsH (V n) u hus)
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim)

end SHEStochastic.NativeCappedApproximation
