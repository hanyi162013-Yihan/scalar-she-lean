module

public import SHEStochastic.ContinuousNormExit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.LocalizedExitBound
open MeasureTheory Set
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- A finite closed norm exit has a level-reaching witness no later
than that exit. This uses the existing continuous exit characterization. -/
theorem reaches (U : ℝ≥0 → Ω → E) (hc : ∀ ω,Continuous (fun t => U t ω))
    (N : ℕ) (H : ℝ≥0) (ω : Ω) (hτ : ContinuousNormExit.exit U N ω≤(H : WithTop ℝ≥0)) :
    ∃ s : ℝ≥0,s≤H ∧ (s : WithTop ℝ≥0)≤ContinuousNormExit.exit U N ω ∧ (N : ℝ)≤‖U s ω‖ := by
  let τ := ContinuousNormExit.exit U N ω
  have hne : τ≠⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτ
  have he : ((τ.untopA : ℝ≥0) : WithTop ℝ≥0)=τ := by
    rw [WithTop.untopA_eq_untop hne,WithTop.coe_untop]
  obtain ⟨s,hs,hN⟩ := (ContinuousNormExit.le_iff U hc N τ.untopA ω).mp he.ge
  exact ⟨s,(WithTop.coe_le_coe.mp (he.le.trans hτ)) |>.trans' hs.2,
    (WithTop.coe_le_coe.mpr hs.2).trans he.le,hN⟩

/-- A pre-exit deterministic envelope gives an explicit probability
bound in terms of its initial and stochastic contributions. -/
theorem probability (μ : Measure Ω) (U : ℝ≥0 → Ω → E)
    (hc : ∀ ω,Continuous (fun t => U t ω)) (N : ℕ) (H : ℝ≥0) (A B : Ω → ℝ)
    (hpre : ∀ᵐ ω ∂μ,∀ s : ℝ≥0,s≤H → (s : WithTop ℝ≥0)≤ContinuousNormExit.exit U N ω → ‖U s ω‖≤A ω+B ω) :
    μ {ω | ContinuousNormExit.exit U N ω≤(H : WithTop ℝ≥0)} ≤
      μ {ω | (N : ℝ)/2≤A ω}+μ {ω | (N : ℝ)/2≤B ω} := by
  apply (measure_mono_ae (t := {ω | (N : ℝ)/2≤A ω}∪{ω | (N : ℝ)/2≤B ω}) ?_).trans (measure_union_le _ _)
  filter_upwards [hpre] with ω hω hτ
  obtain ⟨s,hsH,hsτ,hNs⟩ := reaches U hc N H ω hτ
  have hb := hNs.trans (hω s hsH hsτ)
  change (N : ℝ)/2≤A ω ∨ (N : ℝ)/2≤B ω
  by_cases ha : (N : ℝ)/2≤A ω
  · exact Or.inl ha
  · exact Or.inr (by linarith)

/-- For a vector remainder it is enough to control its finitely many
scalar field suprema. The thresholds stay valid also in dimension zero. -/
theorem finite_fields (μ : Measure Ω) (U : ℝ≥0 → Ω → E)
    (hc : ∀ ω,Continuous (fun t => U t ω)) (N : ℕ) (hN : 0<N) (H : ℝ≥0)
    (A : Ω → ℝ) {n : ℕ} (B : Fin n → Ω → ℝ)
    (hpre : ∀ᵐ ω ∂μ,∀ s : ℝ≥0,s≤H → (s : WithTop ℝ≥0)≤ContinuousNormExit.exit U N ω →
      ‖U s ω‖≤A ω+∑ i,B i ω) :
    μ {ω | ContinuousNormExit.exit U N ω≤(H : WithTop ℝ≥0)} ≤
      μ {ω | (N : ℝ)/2≤A ω}+∑ i,μ {ω | (N : ℝ)/(4*((n : ℝ)+1))<B i ω} := by
  apply (probability μ U hc N H A (fun ω => ∑ i,B i ω) hpre).trans
  apply add_le_add le_rfl
  apply (measure_mono ?_).trans (measure_iUnion_fintype_le μ _)
  intro ω hsum
  simp only [mem_iUnion,mem_setOf_eq]
  by_contra! hb
  have hs : (∑ i,B i ω)≤(n : ℝ)*((N : ℝ)/(4*((n : ℝ)+1))) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  have hn0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hden : (0 : ℝ)<4*((n : ℝ)+1) := by positivity
  have hr : (n : ℝ)*((N : ℝ)/(4*((n : ℝ)+1)))<(N : ℝ)/2 := by
    rw [←mul_div_assoc,div_lt_iff₀ hden]
    nlinarith
  exact not_lt_of_ge hsum (hs.trans_lt hr)

end SHEStochastic.LocalizedExitBound
