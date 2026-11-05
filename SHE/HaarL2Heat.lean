module

public import SHE.HaarLimit

@[expose] public section
set_option autoImplicit false
noncomputable section

/-! The endpoint `rho = 0` estimate for the same signed physical Haar
factor pair. It uses ordinary `L²` input and no fractional inverse bound. -/

namespace SHE.FiniteHaar

open Finset Matrix MeasureTheory AddCircle CircleHeat FiniteTransport
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem signed_prefix_L2 (n k : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k}, ∑ j,
      (referenceFactor n c i.val j - referenceFactor n d i.val j) ^ 2) ≤
        U / m ^ 2 * (((2 ^ k : ℕ) : ℝ)) * ‖gridStep n (c - d)‖ ^ 2 := by
  have hp := signed_prefix_physical n k c d m U hm hc hd
  have he : (∫ y : AddCircle (1 : ℝ), ‖coefficientDifference n c d y‖ ^ 2 ∂haarAddCircle) =
      ‖gridStep n (c - d)‖ ^ 2 := by
    rw [coefficientDifference_L2, gridStep_norm_sq]
    rfl
  rwa [he] at hp

theorem signed_heat_generation_L2 {t : ℝ} (ht : 0 < t)
    (n k : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖heat t (signedGenerationColumn n k c d j)‖ ^ 2) ≤
      (U / m ^ 2 * ‖gridStep n (c - d)‖ ^ 2) * (((2 ^ (k + 1) : ℕ) : ℝ)) *
        min 1 ((((2 ^ (k + 1) : ℕ) : ℝ))⁻¹ ^ 2 / (4 * t)) := by
  have hp := signed_prefix_L2 n (k + 1) c d m U hm hc hd
  have hg := generation_energy_le_prefix n k (referenceFactor n c - referenceFactor n d)
  calc
    _ ≤ ∑ j : Option (DetailIndex n),
        min 1 ((((2 ^ (k + 1) : ℕ) : ℝ))⁻¹ ^ 2 / (4 * t)) * ‖signedGenerationColumn n k c d j‖ ^ 2 :=
      sum_le_sum (fun j _ => heat_generationSynthesis_sq ht n k _)
    _ = _ * (∑ j : Option (DetailIndex n), ‖signedGenerationColumn n k c d j‖ ^ 2) :=
      (mul_sum _ _ _).symm
    _ ≤ _ * (U / m ^ 2 * (((2 ^ (k + 1) : ℕ) : ℝ)) * ‖gridStep n (c - d)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hg.trans hp) (le_min (by norm_num) (by positivity))
    _ = _ := by ring

theorem heatedLevelColumns_L2_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (n r : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    ‖heatedLevelColumns n r c d t‖ ≤
      Real.sqrt (U / m ^ 2 * ‖gridStep n (c - d)‖ ^ 2) *
        DyadicTransport.smoothingTerm (t ^ (-(1 / 2 : ℝ))) (1 / 2) r := by
  let C := U / m ^ 2 * ‖gridStep n (c - d)‖ ^ 2
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have hC : 0 ≤ C := mul_nonneg (div_nonneg hU (sq_nonneg m)) (sq_nonneg _)
  have he (r : ℕ) : DyadicTransport.massiveTerm (t ^ (-(1 / 2 : ℝ))) 0 0 r =
      DyadicTransport.smoothingTerm (t ^ (-(1 / 2 : ℝ))) (1 / 2) r := by
    simp [DyadicTransport.massiveTerm, DyadicTransport.smoothingTerm]
  rw [← Real.sqrt_sq (norm_nonneg (heatedLevelColumns n r c d t)), ← he r]
  cases r with
  | zero =>
    apply constant_generation_sqrt_bound (sq_nonneg _) hC ht ht1 (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0)
    simp only [Real.rpow_zero, mul_one]
    rw [heatedLevelColumns_norm_sq]
    have hp := signed_prefix_L2 n 0 c d m U hm hc hd
    have hg := level_energy_le_prefix n 0 (referenceFactor n c - referenceFactor n d)
    calc
      _ ≤ ∑ j : Option (DetailIndex n), ‖levelSynthesis n 0
          (fun i => referenceFactor n c i j - referenceFactor n d i j)‖ ^ 2 :=
        sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (heat_contraction t _) 2)
      _ ≤ _ := hg.trans (hp.trans_eq (by simp [C]))
  | succ k =>
    apply generation_sqrt_bound (k + 1) (sq_nonneg _) hC ht (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0)
    simp only [Real.rpow_zero, mul_one]
    rw [heatedLevelColumns_norm_sq]
    have hh := signed_heat_generation_L2 ht n k c d m U hm hc hd
    have hlevel (x : Option (DetailIndex n) → ℝ) : levelSynthesis n (k + 1) x = generationSynthesis n k x := rfl
    simp_rw [hlevel]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, signedGenerationColumn, C] using hh

theorem signed_heat_finite_HS_L2 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (n : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    ‖heatedSignedColumns n c d t‖ ≤ Real.sqrt (U / m ^ 2 * ‖gridStep n (c - d)‖ ^ 2) *
      DyadicTransport.smoothingConstant (1 / 2) * t ^ (-(1 / 4 : ℝ)) := by
  let C := Real.sqrt (U / m ^ 2 * ‖gridStep n (c - d)‖ ^ 2)
  have hA : 1 ≤ t ^ (-(1 / 2 : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hs := DyadicTransport.smoothing_series hA (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  rw [heatedSignedColumns_levels]
  calc
    _ ≤ ∑ r ∈ range (n + 1), ‖heatedLevelColumns n r c d t‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ range (n + 1), C * DyadicTransport.smoothingTerm (t ^ (-(1 / 2 : ℝ))) (1 / 2) r :=
      sum_le_sum (fun r _ => heatedLevelColumns_L2_bound ht ht1 n r c d m U hm hc hd)
    _ = C * ∑ r ∈ range (n + 1), DyadicTransport.smoothingTerm (t ^ (-(1 / 2 : ℝ))) (1 / 2) r :=
      (mul_sum _ _ _).symm
    _ ≤ C * ∑' r, DyadicTransport.smoothingTerm (t ^ (-(1 / 2 : ℝ))) (1 / 2) r := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact hs.1.sum_le_tsum _ (fun r _ => by unfold DyadicTransport.smoothingTerm; positivity)
    _ ≤ C * (DyadicTransport.smoothingConstant (1 / 2) * (t ^ (-(1 / 2 : ℝ))) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hs.2 (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.rpow_mul ht.le]
      rw [show (-(1 / 2 : ℝ)) * (1 / 2) = -(1 / 4 : ℝ) by ring]
      change C * (DyadicTransport.smoothingConstant (1 / 2) * t ^ (-(1 / 4 : ℝ))) =
        C * DyadicTransport.smoothingConstant (1 / 2) * t ^ (-(1 / 4 : ℝ))
      ring

def signedL2HeatConstant (m U : ℝ) : ℝ := U / m ^ 2 * (DyadicTransport.smoothingConstant (1 / 2)) ^ 2

theorem signed_heat_finite_HS_L2_sq {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (n : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖heat t (signedColumn n c d j)‖ ^ 2) ≤
      signedL2HeatConstant m U * t ^ (-(1 / 2 : ℝ)) * ‖gridStep n (c - d)‖ ^ 2 := by
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have hC : 0 ≤ U / m ^ 2 * ‖gridStep n (c - d)‖ ^ 2 :=
    mul_nonneg (div_nonneg hU (sq_nonneg m)) (sq_nonneg _)
  have hh := pow_le_pow_left₀ (norm_nonneg _) (signed_heat_finite_HS_L2 ht ht1 n c d m U hm hc hd) 2
  rw [heatedSignedColumns_norm_sq, mul_pow, mul_pow, Real.sq_sqrt hC] at hh
  have hp : (t ^ (-(1 / 4 : ℝ))) ^ 2 = t ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_mul_natCast ht.le]
    norm_num
  rw [hp] at hh
  exact hh.trans_eq (by unfold signedL2HeatConstant; ring)

/-- The genuine common-Haar, countable signed heat estimate with ordinary
`L²` coefficient difference. This is the `rho = 0` companion-construction
bound and uses exactly the same factor pair as the negative-input theorem. -/
theorem global_signed_heat_L2 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hgbound : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedL2HeatConstant m U * t ^ (-(1 / 2 : ℝ)) * ‖f - g‖ ^ 2 := by
  let c : ∀ N, Grid N → ℝ := fun N => localAverage N f
  let d : ∀ N, Grid N → ℝ := fun N => localAverage N g
  have hc (N : ℕ) (x : Grid N) : m ≤ c N x ∧ c N x ≤ U := localAverage_bounds_ae N f m U hfbound x
  have hd (N : ℕ) (x : Grid N) : m ≤ d N x ∧ d N x ≤ U := localAverage_bounds_ae N g m U hgbound x
  have hcf : Filter.Tendsto (fun N => gridStep N (c N)) Filter.atTop (nhds f) :=
    DyadicApproximation.average_tendsto_of_real f hfreal
  have hdg : Filter.Tendsto (fun N => gridStep N (d N)) Filter.atTop (nhds g) :=
    DyadicApproximation.average_tendsto_of_real g hgreal
  have hdiff : Filter.Tendsto (fun N => gridStep N (c N - d N)) Filter.atTop (nhds (f - g)) := by
    simpa only [gridStep_sub] using hcf.sub hdg
  let B : ℕ → ℝ := fun N => signedL2HeatConstant m U * t ^ (-(1 / 2 : ℝ)) * ‖gridStep N (c N - d N)‖ ^ 2
  have hB : Filter.Tendsto B Filter.atTop
      (nhds (signedL2HeatConstant m U * t ^ (-(1 / 2 : ℝ)) * ‖f - g‖ ^ 2)) :=
    (hdiff.norm.pow 2).const_mul _
  have hfinite (s : Finset HaarNode) :
      (∑ q ∈ s, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedL2HeatConstant m U * t ^ (-(1 / 2 : ℝ)) * ‖f - g‖ ^ 2 := by
    have hlim : Filter.Tendsto (fun N => ∑ q ∈ s, ‖finiteNodeColumn N (c N) (d N) t q‖ ^ 2)
        Filter.atTop (nhds (∑ q ∈ s, ‖heat t (globalSignedColumn q f g)‖ ^ 2)) :=
      tendsto_finsetSum s (fun q _ => (finiteNodeColumn_tendsto t q c d f g m U hm hc hd hcf hdg).norm.pow 2)
    apply le_of_tendsto_of_tendsto hlim hB
    exact Filter.Eventually.of_forall (fun N => (finiteNodeColumn_sum_le N (c N) (d N) t s).trans
      (signed_heat_finite_HS_L2_sq ht ht1 N (c N) (d N) m U hm (hc N) (hd N)))
  have hs : Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs, Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite⟩

theorem global_signed_heat_L2_tail {t : ℝ} (ht : 1 ≤ t)
    (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hgreal : ∀ᵐ y ∂haarAddCircle, (g y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hgbound : ∀ᵐ y ∂haarAddCircle, m ≤ (g y).re ∧ (g y).re ≤ U) :
    Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedL2HeatConstant m U * ‖f - g‖ ^ 2 := by
  have hone := global_signed_heat_L2 (by norm_num : (0 : ℝ) < 1) le_rfl
    f g m U hm hfreal hgreal hfbound hgbound
  have hs : Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ => heat_sq_le_at_one ht _) hone.1
  refine ⟨hs, (hs.tsum_le_tsum (fun _ => heat_sq_le_at_one ht _) hone.1).trans ?_⟩
  simpa only [Real.one_rpow, mul_one] using hone.2

end SHE.FiniteHaar
