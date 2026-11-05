module

public import SHE.NormalizedOffsetWeights
public import SHE.NoFreshOffsetCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PairedOffsetBudgets
open Set MeasureTheory Real
open scoped BigOperators
variable {Ω:Type*} [MeasurableSpace Ω] {m r:ℕ}

/-- Any endpoint choice for each original leaf is controlled by the SUM
of the two ORIGINAL normalized budgets. No full-reference baseline is
replaced by a reduced Gaussian-law baseline. -/
theorem offset_le_sum (age oldOffset newOffset:Fin m→ℝ)
    (power degree:ℝ) (hage:∀j,0<age j) (choose:Fin m→Bool) (j:Fin m) :
    |(if choose j then newOffset j else oldOffset j)|^power≤
      (NormalizedLeafOffsets.budget age oldOffset power degree+
        NormalizedLeafOffsets.budget age newOffset power degree)*(age j)^degree := by
  have ho:=NormalizedLeafOffsets.offset_le_budget age oldOffset power degree hage j
  have hn:=NormalizedLeafOffsets.offset_le_budget age newOffset power degree hage j
  have ho0:=NormalizedLeafOffsets.budget_nonneg age oldOffset power degree hage
  have hn0:=NormalizedLeafOffsets.budget_nonneg age newOffset power degree hage
  have ha:0≤(age j)^degree:=rpow_nonneg (hage j).le _
  split_ifs
  · exact hn.trans (mul_le_mul_of_nonneg_right (by linarith) ha)
  · exact ho.trans (mul_le_mul_of_nonneg_right (by linarith) ha)

/-- A genuine past-weighted two-endpoint offset packet stays LINEAR.
This is the budget required for all mixed endpoint product telescopes. -/
theorem weighted_sum (μ:Measure Ω) (oldBudget newBudget weight:Ω→ℝ)
    (ho:Integrable (fun ω=>weight ω*oldBudget ω) μ)
    (hn:Integrable (fun ω=>weight ω*newBudget ω) μ)
    (C0 C1:ℝ)
    (hbo:(∫ω,weight ω*oldBudget ω ∂μ)≤C0*(∫ω,weight ω ∂μ))
    (hbn:(∫ω,weight ω*newBudget ω ∂μ)≤C1*(∫ω,weight ω ∂μ)) :
    Integrable (fun ω=>weight ω*(oldBudget ω+newBudget ω)) μ ∧
      (∫ω,weight ω*(oldBudget ω+newBudget ω) ∂μ)≤(C0+C1)*(∫ω,weight ω ∂μ) := by
  simp only [mul_add]
  refine ⟨ho.add hn,?_⟩
  rw [integral_add ho hn]
  nlinarith

/-- The root-paired full Gaussian word constant averages against the
actual correlated past weight using only its two endpoint offset budgets. -/
theorem root_constant_weighted (μ:Measure Ω) (P:CanonicalCovariance.ProfileParameters)
    (choices:List (Fin r×Fin (m+1))) (b:ℕ) (budget weight:Ω→ℝ)
    (hw:Integrable weight μ) (hi:Integrable (fun ω=>weight ω*budget ω) μ)
    (Cbar:ℝ) (hb:(∫ω,weight ω*budget ω ∂μ)≤Cbar*(∫ω,weight ω ∂μ)) :
    Integrable (fun ω=>weight ω*NoFreshAssignedMoments.constant P r m choices b (budget ω)) μ ∧
      (∫ω,weight ω*NoFreshAssignedMoments.constant P r m choices b (budget ω) ∂μ)≤
        NoFreshAssignedMoments.constant P r m choices b Cbar*(∫ω,weight ω ∂μ) := by
  have he:(fun ω=>weight ω*NoFreshAssignedMoments.constant P r m choices b (budget ω))=
      (fun ω=>weight ω*NoFreshAssignedMoments.constant P r m choices b 0+
        NoFreshAssignedMoments.offsetSlope b choices*(weight ω*budget ω)) := by
    funext ω
    rw [NoFreshAssignedMoments.constant_affine]
    ring
  rw [he]
  refine ⟨(hw.mul_const _).add (hi.const_mul _),?_⟩
  rw [integral_add (hw.mul_const _) (hi.const_mul _),integral_mul_const,integral_const_mul,
    NoFreshAssignedMoments.constant_affine P b choices Cbar]
  have hh:=mul_le_mul_of_nonneg_left hb (NoFreshAssignedMoments.offsetSlope_nonneg b choices)
  nlinarith

end SHE.PairedOffsetBudgets
