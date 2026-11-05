module

public import SHE.IntervalGramRange

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.IntervalHistoryEnergy
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures
  StoppedFourier OldIntervalCovariance GaussianGramScore
open scoped BigOperators InnerProductSpace
local instance intervalHistoryEnergy_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def active (σ : Fin n → ℝ) (hi : ℝ) : Finset (Fin n) := Finset.univ.filter (fun i => hi ≤ σ i)

theorem historyF_active (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (z : Fin n → ℂ) {lo hi r : ℝ} (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i) (hr : lo ≤ r) :
    historyF Finset.univ z σ target center r = historyF (active σ hi) z σ target center r := by
  classical
  simp only [historyF, active, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi'
  by_cases ha : hi ≤ σ i
  · simp only [ha, ite_true]
  · have hs := (hstop i).resolve_right ha
    have hn : ¬ r < σ i := not_lt.mpr (hs.trans hr)
    simp only [ha, hn, ite_false]

/-- Coherent old heat histories grow in spatial L² towards the upper end
of an interval. Already stopped coordinates are filtered out exactly. -/
theorem endpoint_norm_sq_le (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (z : Fin n → ℂ) {lo hi r : ℝ}
    (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i) (hr : lo ≤ r) (hrhi : r < hi) :
    ‖historyF Finset.univ z σ target center lo‖ ^ 2 ≤
      ‖historyF Finset.univ z σ target center r‖ ^ 2 := by
  rw [historyF_active σ target center z hstop le_rfl, historyF_active σ target center z hstop hr]
  exact historyF_before_first_stop (active σ hi) z σ target center (fun i _ => hages i) hr
    (fun i hi' => hrhi.trans_le (Finset.mem_filter.mp hi').2)

theorem endpoint_energy_le (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (z : Fin n → ℂ) {lo hi : ℝ} (hgap : lo < hi)
    (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i) :
    (hi - lo) * ‖historyF Finset.univ z σ target center lo‖ ^ 2 ≤
      ∫ r in lo..hi, ‖historyF Finset.univ z σ target center r‖ ^ 2 := by
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hgap.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖historyF Finset.univ z σ target center lo‖ ^ 2) volume lo hi)
    (historyF_norm_sq_intervalIntegrable Finset.univ z σ target center (fun i _ => hages i) lo hi)
    (fun r hr => endpoint_norm_sq_le σ target center hages z hstop hr.1.le hr.2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

theorem real_endpoint_energy_le (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (z : State n) {lo hi : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
    (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i) :
    (hi - lo) * (∫ x, realHistory σ target center z (lo,x) ^ 2 ∂haarAddCircle) ≤
      ∫ p, realHistory σ target center z p ^ 2 ∂intervalMeasure lo hi := by
  have hInt : Integrable (fun p => realHistory σ target center z p ^ 2) (intervalMeasure lo hi) := by
    rw [intervalMeasure_eq_restrict hlo]
    exact (realHistory_square_product_integrable σ target center hages z 0).restrict
  rw [intervalMeasure, integral_prod _ hInt]
  simp_rw [realHistory_square_mass σ target center hages z]
  rw [← intervalIntegral.integral_of_le hgap.le]
  exact endpoint_energy_le σ target center hages (fun i => (z i : ℂ)) hgap hstop

theorem weighted_endpoint_energy_le (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (z : State n) {lo hi ell M : ℝ}
    (hlo : 0 ≤ lo) (hgap : lo < hi) (hstop : ∀ i, σ i ≤ lo ∨ hi ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (hell : 0 < ell) (hb : ∀ p, ell ≤ c p ∧ c p ≤ M) :
    ell * (hi - lo) * (∫ x, realHistory σ target center z (lo,x) ^ 2 ∂haarAddCircle) ≤
      ∫ p, c p * realHistory σ target center z p ^ 2 ∂intervalMeasure lo hi := by
  have hInt : Integrable (fun p => realHistory σ target center z p ^ 2) (intervalMeasure lo hi) := by
    rw [intervalMeasure_eq_restrict hlo]
    exact (realHistory_square_product_integrable σ target center hages z 0).restrict
  have hC : Integrable (fun p => c p * realHistory σ target center z p ^ 2) (intervalMeasure lo hi) :=
    hInt.bdd_mul hc.aestronglyMeasurable (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hell.le.trans (hb p).1)]
      exact (hb p).2))
  have hmono := integral_mono (hInt.const_mul ell) hC
    (fun p => mul_le_mul_of_nonneg_right (hb p).1 (sq_nonneg _))
  rw [integral_const_mul] at hmono
  have he := mul_le_mul_of_nonneg_left (real_endpoint_energy_le σ target center hages z hlo hgap hstop) hell.le
  have he' : ell * (hi - lo) * (∫ x, realHistory σ target center z (lo,x) ^ 2 ∂haarAddCircle) ≤
      ell * (∫ p, realHistory σ target center z p ^ 2 ∂intervalMeasure lo hi) := by
    simpa only [mul_assoc] using he
  exact he'.trans hmono

end SHE.IntervalHistoryEnergy
