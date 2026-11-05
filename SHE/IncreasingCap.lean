module

public import SHE.RealMomentBound
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.IncreasingCap
open Set Filter MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform integral bounds on genuine increasing finite caps imply
the full integrability and bound. The cap may depend on the same sample
as the integrand; no independence or uniform pathwise cap is required. -/
theorem integral_bound (μ : Measure Ω) (E C : Ω→ℝ) (hE : Measurable E) (hC : Measurable C)
    (hE0 : ∀ ω,0≤E ω) {K : ℝ} (hK : 0≤K)
    (hi : ∀ n : ℕ,Integrable (fun ω => if C ω≤(n:ℝ) then E ω else 0) μ)
    (hb : ∀ n : ℕ,(∫ ω,if C ω≤(n:ℝ) then E ω else 0 ∂μ)≤K) :
    Integrable E μ ∧ (∫ ω,E ω ∂μ)≤K := by
  let f : ℕ→Ω→ℝ≥0∞ := fun n ω => if C ω≤(n:ℝ) then ENNReal.ofReal (E ω) else 0
  have hm (n : ℕ) : Measurable (f n) :=
    (ENNReal.continuous_ofReal.measurable.comp hE).ite (measurableSet_le hC measurable_const) measurable_const
  have hmono : Monotone f := by
    intro n m hnm ω
    by_cases hn : C ω≤(n:ℝ)
    · have hcm : C ω≤(m:ℝ) := hn.trans (by exact_mod_cast hnm)
      simp only [f,ite_eq_left hn,ite_eq_left hcm,le_rfl]
    · simp only [f,ite_eq_right hn,zero_le]
  have hs (ω : Ω) : (⨆ n,f n ω)=ENNReal.ofReal (E ω) := by
    apply le_antisymm
    · exact iSup_le (fun n => by dsimp only [f];split_ifs <;> simp)
    · obtain ⟨n,hn⟩ := exists_nat_ge (C ω)
      exact le_iSup_of_le n (by simp only [f,ite_eq_left hn,le_rfl])
  apply RealMomentBound.integral_bound μ E hE.aestronglyMeasurable hE0 hK
  rw [←show (fun ω=>⨆ n,f n ω)=fun ω=>ENNReal.ofReal (E ω) from funext hs,lintegral_iSup hm hmono]
  apply iSup_le
  intro n
  have hpos (ω : Ω) : 0 ≤ if C ω≤(n:ℝ) then E ω else 0 := by split_ifs <;> simp [hE0]
  have he := ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all _ hpos)
  have hfn : (fun ω=>ENNReal.ofReal (if C ω≤(n:ℝ) then E ω else 0))=f n := by
    funext ω
    by_cases hn : C ω≤(n:ℝ)
    · simp only [f,ite_eq_left hn]
    · simp only [f,ite_eq_right hn,ENNReal.ofReal_zero]
  rw [hfn] at he
  exact he.symm.trans_le (ENNReal.ofReal_le_ofReal (hb n))

end SHE.IncreasingCap
