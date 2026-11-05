module

public import SHE.SmoothApproximation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ProfileCoefficientStability
open MeasureTheory ProbabilityTheory Set Filter GaussianProfile ParametricProfile ProfileVariance
open scoped Topology

theorem gaussianAverage_coefficient_bound {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    {M ε : ℝ} (haB : ∀ z,|a z| ≤ M) (hbB : ∀ z,|b z| ≤ M)
    (hd : ∀ z,|a z-b z| ≤ ε) (m v : ℝ) :
    |gaussianAverage a m v-gaussianAverage b m v| ≤ ε := by
  have hi (f : ℝ → ℝ) (hf : Measurable f) (hB : ∀ z,|f z| ≤ M) :
      Integrable (fun z => f (m+z)) (gaussianReal 0 v.toNNReal) := by
    apply (integrable_const M).mono' (hf.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by change |f (m+z)| ≤ M; exact hB (m+z))
  rw [gaussianAverage,gaussianAverage,← integral_sub (hi a ha haB) (hi b hb hbB)]
  have hh := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v.toNNReal)
    (f := fun z => a (m+z)-b (m+z)) (C := ε)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hd (m+z)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

section Uniform
variable {X : Type*} [MeasurableSpace X] {a b : ℝ → ℝ} {Φ : X × Domain → ℝ}
variable {ell M H β h ε : ℝ}

/-- Uniform coefficient perturbations propagate through the actual Picard
scheme with the contraction constant, uniformly over every initial mean. -/
theorem picard_coefficient_bound (ha : Measurable a) (hb : Measurable b) (hΦ : Measurable Φ)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh1 : h ≤ 1) (hal : ∀ z,ell ≤ a z) (hau : ∀ z,a z ≤ M)
    (hbl : ∀ z,ell ≤ b z) (hbu : ∀ z,b z ≤ M)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
    (hsmall : contractionConstant ell H β*h^(β/4) ≤ 1/2)
    (hε : 0 ≤ ε) (hd : ∀ z,|a z-b z| ≤ ε) (n : ℕ) (p : X × Domain) :
    |picard a Φ ell h n p-picard b Φ ell h n p| ≤ 2*ε := by
  have haB : ∀ z,|a z| ≤ M := fun z => by rw [abs_of_nonneg (hell.le.trans (hal z))]; exact hau z
  have hbB : ∀ z,|b z| ≤ M := fun z => by rw [abs_of_nonneg (hell.le.trans (hbl z))]; exact hbu z
  induction n generalizing p with
  | zero => simpa only [picard,sub_self,abs_zero] using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hε
  | succ n ih =>
    by_cases hp : p.2.1 ∈ Ioc 0 h
    · simp only [picard,update,ite_eq_left hp]
      let c : Domain → ℝ := fun q => picard a Φ ell h n (p.1,q)
      let d : Domain → ℝ := fun q => picard b Φ ell h n (p.1,q)
      have hc : Measurable c := (picard_measurable ha hΦ ell h n).comp (measurable_const.prodMk measurable_id)
      have hdm : Measurable d := (picard_measurable hb hΦ ell h n).comp (measurable_const.prodMk measurable_id)
      have hcB := fun q => picard_elliptic (Φ := Φ) (h := h) ha hell.le hM hal hau n (p.1,q)
      have hdB := fun q => picard_elliptic (Φ := Φ) (h := h) hb hell.le hM hbl hbu n (p.1,q)
      have he := profileUpdate_contraction (φ := fun q => Φ (p.1,q)) ha hc hdm hp.1 (hp.2.trans hh1)
        hell hM hH hβ.le (by linarith : β ≤ 2) (mul_nonneg (by norm_num) hε) haB hholder
        (fun s _ y => (hcB (s,y)).1) (fun s _ y => (hcB (s,y)).2)
        (fun s _ y => (hdB (s,y)).1) (fun s _ y => (hdB (s,y)).2)
        (fun s _ y => ih (p.1,(s,y))) p.2.2
      have hq : contractionConstant ell H β*p.2.1^(β/4) ≤ 1/2 := by
        exact (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hp.1.le hp.2 (by positivity))
          (contractionConstant_nonneg hell.le hH)).trans hsmall
      have he' : |gaussianAverage a (Φ p) (positiveVarianceFamily (picard a Φ ell h n) p)-
          gaussianAverage a (Φ p) (positiveVarianceFamily (picard b Φ ell h n) p)| ≤ ε := by
        rw [positiveVarianceFamily,positiveVarianceFamily,positiveVarianceMap_eq hp.1.le,
          positiveVarianceMap_eq hp.1.le]
        change |profileUpdate a (fun q => Φ (p.1,q)) c p.2.1 p.2.2-
          profileUpdate a (fun q => Φ (p.1,q)) d p.2.1 p.2.2| ≤ ε
        have hm := mul_le_mul_of_nonneg_right hq (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hε)
        exact he.trans (by nlinarith [hm])
      have he'' := gaussianAverage_coefficient_bound ha hb haB hbB hd (Φ p)
        (positiveVarianceFamily (picard b Φ ell h n) p)
      exact (abs_sub_le _ _ _).trans ((add_le_add he' he'').trans (by ring_nf; exact le_rfl))
    · simp only [picard,update,ite_eq_right hp,sub_self,abs_zero]
      positivity

theorem canonical_coefficient_bound (ha : Measurable a) (hb : Measurable b) (hΦ : Measurable Φ)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hal : ∀ z,ell ≤ a z) (hau : ∀ z,a z ≤ M)
    (hbl : ∀ z,ell ≤ b z) (hbu : ∀ z,b z ≤ M)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
    (hholderb : ∀ z w,|b z-b w| ≤ H*|z-w|^β)
    (hsmall : contractionConstant ell H β*h^(β/4) ≤ 1/2)
    (hε : 0 ≤ ε) (hd : ∀ z,|a z-b z| ≤ ε) (p : X × Domain) :
    |canonicalProfile a Φ ell h p-canonicalProfile b Φ ell h p| ≤ 2*ε := by
  have ht := (picard_tendsto_canonical ha hΦ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall p).sub
    (picard_tendsto_canonical hb hΦ hell hM hH hβ hβ1 hh hh1 hbl hbu hholderb hsmall p)
  exact le_of_tendsto ht.abs (Eventually.of_forall (fun n => picard_coefficient_bound
    ha hb hΦ hell hM hH hβ hβ1 hh1 hal hau hbl hbu hholder hsmall hε hd n p))

end Uniform
end SHE.ProfileCoefficientStability
