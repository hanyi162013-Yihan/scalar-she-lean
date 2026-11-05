module

public import MathFin.Foundations.GirsanovPredictableTheta

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.ConvergenceInMeasureAlgebra
open MeasureTheory Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A continuous function of two real variables preserves convergence in
measure. Reuses the public common-subsequence theorem. -/
theorem continuous_map₂ {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop F) (hg : TendstoInMeasure μ g atTop G)
    (hmf : ∀ n, AEStronglyMeasurable (f n) μ) (hmg : ∀ n, AEStronglyMeasurable (g n) μ)
    (Φ : ℝ × ℝ → ℝ) (hΦ : Continuous Φ) :
    TendstoInMeasure μ (fun n ω ↦ Φ (f n ω, g n ω)) atTop (fun ω ↦ Φ (F ω, G ω)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n ↦
    hΦ.comp_aestronglyMeasurable ((hmf n).prodMk (hmg n)))).mpr
  intro ns hns
  obtain ⟨ms, hms, hfa, hga⟩ := MathFin.exists_subseq_tendsto_ae₂ hf hg ns hns.tendsto_atTop
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hfa, hga] with ω hfω hgω
  exact (hΦ.continuousAt.tendsto).comp (hfω.prodMk_nhds hgω)

theorem continuous_map {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop F) (hmf : ∀ n, AEStronglyMeasurable (f n) μ)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    TendstoInMeasure μ (fun n ω ↦ φ (f n ω)) atTop (fun ω ↦ φ (F ω)) := by
  exact continuous_map₂ hf hf hmf hmf (fun p ↦ φ p.1) (hφ.comp continuous_fst)

/-- Finite sums preserve convergence in measure. -/
theorem finset_sum {κ : Type*} (S : Finset κ) {f : κ → ℕ → Ω → ℝ} {F : κ → Ω → ℝ}
    (hf : ∀ k, TendstoInMeasure μ (f k) atTop (F k))
    (hm : ∀ k n, AEStronglyMeasurable (f k n) μ) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ S, f k n ω) atTop (fun ω ↦ ∑ k ∈ S, F k ω) := by
  classical
  induction S using Finset.induction with
  | empty =>
      simpa only [Finset.sum_empty] using tendstoInMeasure_of_tendsto_ae
        (fun _ : ℕ ↦ (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω ↦ (0 : ℝ)) μ))
        (Filter.Eventually.of_forall fun _ ↦ tendsto_const_nhds)
  | @insert a S ha ih =>
      have hh := continuous_map₂ (hf a) ih (hm a)
        (fun n ↦ S.aestronglyMeasurable_fun_sum (fun k hk ↦ hm k n))
        (fun p ↦ p.1 + p.2) (continuous_fst.add continuous_snd)
      simpa only [Finset.sum_insert ha] using hh

end SHEStochastic.ConvergenceInMeasureAlgebra
