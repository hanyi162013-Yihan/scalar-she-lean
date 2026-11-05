module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Compact

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.FiniteMarginalTightness
open MeasureTheory Set
open scoped ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)] [∀ i, T2Space (E i)] [∀ i, SecondCountableTopology (E i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

/-- Tight coordinate families give tight joint laws without independence.
The original joint coupling is retained. -/
theorem tight_varying (μ : ℕ → Measure Ω) (Y : ℕ → Ω → ∀ i, E i) (hY : ∀ k, Measurable (Y k))
    (ht : ∀ i, IsTightMeasureSet (Set.range (fun k => (μ k).map (fun ω => Y k ω i)))) :
    IsTightMeasureSet (Set.range (fun k => (μ k).map (Y k))) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞)+1
  have hc0 : c ≠ 0 := by positivity
  have hct : c ≠ ⊤ := by simp [c]
  have hδ : 0 < ε/c := ENNReal.div_pos hε.ne' hct
  choose K hK hb using fun i =>
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (ht i)) (ε/c) hδ
  refine ⟨Set.univ.pi K,isCompact_univ_pi hK,?_⟩
  rintro ν ⟨k,rfl⟩
  have hm (i : ι) : Measurable (fun ω => Y k ω i) := (measurable_pi_apply i).comp (hY k)
  have he : (Y k) ⁻¹' (Set.univ.pi K)ᶜ = ⋃ i, (fun ω => Y k ω i) ⁻¹' (K i)ᶜ := by
    ext ω
    simp
  rw [Measure.map_apply (hY k) (isCompact_univ_pi hK).isClosed.measurableSet.compl,he]
  calc
    _ ≤ ∑ i, (μ k) ((fun ω => Y k ω i) ⁻¹' (K i)ᶜ) := measure_iUnion_fintype_le (μ k) _
    _ = ∑ i, ((μ k).map (fun ω => Y k ω i)) (K i)ᶜ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Measure.map_apply (hm i) (hK i).isClosed.measurableSet.compl).symm
    _ ≤ ∑ _ : ι, ε/c := Finset.sum_le_sum (fun i _ => hb i _ (Set.mem_range_self k))
    _ = (Fintype.card ι : ℝ≥0∞)*(ε/c) := by simp [nsmul_eq_mul]
    _ ≤ c*(ε/c) := by gcongr; exact le_add_of_nonneg_right zero_le_one
    _ = ε := ENNReal.mul_div_cancel hc0 hct

/-- Common-measure specialization, retaining the original interface. -/
theorem tight (μ : Measure Ω) (Y : ℕ → Ω → ∀ i, E i) (hY : ∀ k, Measurable (Y k))
    (ht : ∀ i, IsTightMeasureSet (Set.range (fun k => μ.map (fun ω => Y k ω i)))) :
    IsTightMeasureSet (Set.range (fun k => μ.map (Y k))) :=
  tight_varying (fun _ => μ) Y hY ht

end SHEStochastic.FiniteMarginalTightness
