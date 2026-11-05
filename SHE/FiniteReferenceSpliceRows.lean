module

public import SHE.FiniteReferenceSplicePast

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section
namespace SHE.FiniteReferenceSplice
open Set MeasureTheory PredictableL2 StoppedItoInputs PastItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {n : ℕ} (v : ℝ≥0) (R S : Fin n → Process (E:=C) 𝓕 μ H)

/-- One original predictable-space event identifies every frozen row
strictly after v. No independent copy of the noise is introduced. -/
theorem rows_after_past_ae : ∀ᵐ p ∂energyMeasure μ H,v<p.1 → ∀ i,
    rows 𝓕 μ H v R S i p=S i p := by
  have he (i) := ae_eq_of_ae_eq_trim (Lp.coeFn_add
    (stop 𝓕 μ H (v:ℝ) (R i)) (post 𝓕 μ H v (S i)))
  filter_upwards [ae_all_iff.mpr (fun i => stop_ae 𝓕 μ H (v:ℝ) (R i)),
    ae_all_iff.mpr (fun i => post_ae 𝓕 μ H v (S i)),ae_all_iff.mpr he] with p hs hp he hvr i
  change (stop 𝓕 μ H (v:ℝ) (R i)+post 𝓕 μ H v (S i)) p=S i p
  rw [he i]
  simp only [Pi.add_apply,hs i,hp i,indicator_apply,before,mem_ofPred_eq,NNReal.coe_lt_coe,
    not_lt.mpr hvr.le,ite_false,hvr,ite_true,zero_add]

/-- The first/reference martingale difference has exactly TWO complete
noise terms: the signed input and the gradient displacement. Both use
the same original rows and retain all correlations. -/
theorem complete_gradient_row_ae (f g : ℝ≥0×Ω → Fin n → ℝ) :
    ∀ᵐ p ∂energyMeasure μ H,v<p.1 →
      (∑ j : Fin (n+n),(Fin.append (f p) (fun i => -g p i) j) • jointRows 𝓕 μ H v R S j p)=
      (∑ i : Fin n,f p i • (R i p-S i p))+
        ∑ i : Fin n,(f p i-g p i) • S i p := by
  filter_upwards [rows_after_past_ae 𝓕 μ H v R S] with p hp hvp
  rw [Fin.sum_univ_add]
  simp only [jointRows,Fin.append_left,Fin.append_right,hp hvp]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  module

end SHE.FiniteReferenceSplice
