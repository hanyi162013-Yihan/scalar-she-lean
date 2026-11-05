module

public import SHE.HaarLimit

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar

open Finset Matrix MeasureTheory AddCircle CircleHeat FiniteTransport
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem gridStep_inner_complex (n : ℕ) (a b : Grid n → ℝ) :
    inner ℂ (gridStep n a) (gridStep n b) =
      (((((2 ^ n : ℕ) : ℝ))⁻¹ * ∑ x, a x * b x : ℝ) : ℂ) := by
  apply Complex.ext
  · exact gridStep_inner n a b
  · have hi := integral_im (L2.integrable_inner (𝕜 := ℂ) (gridStep n a) (gridStep n b))
    rw [← L2.inner_def] at hi
    have hz : (∫ y, (inner ℂ (gridStep n a y) (gridStep n b y)).im ∂haarAddCircle) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [gridStep_ae_cellIndex n a, gridStep_ae_cellIndex n b] with y ha hb
      simp [ha, hb, RCLike.inner_apply]
    change RCLike.im (inner ℂ (gridStep n a) (gridStep n b)) = 0
    exact hi.symm.trans hz

def normalizedCell (n : ℕ) (x : Grid n) : CircleL2 :=
  (Real.sqrt (((2 ^ n : ℕ) : ℝ)) : ℂ) • gridStep n (Pi.single x 1)

theorem normalizedCell_orthonormal (n : ℕ) : Orthonormal ℂ (normalizedCell n) := by
  rw [orthonormal_iff_ite]
  intro x y
  rw [normalizedCell, normalizedCell, inner_smul_left, inner_smul_right, gridStep_inner_complex]
  have hN : (0 : ℝ) < (((2 ^ n : ℕ) : ℝ)) := by positivity
  by_cases hxy : x = y
  · subst y
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
    simp only [sum_ite_eq', mem_univ, ite_true, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt hN.le]
    simp
  · simp [Pi.single_apply, hxy, Ne.symm hxy]

theorem gridStep_cell_expansion (n : ℕ) (a : Grid n → ℝ) :
    gridStep n a = ∑ x : Grid n, a x • gridStep n (Pi.single x 1) := by
  have hlin := map_sum (gridStepLinear n) (fun x : Grid n => a x • Pi.single x 1) univ
  simp only [map_smul] at hlin
  change gridStep n (∑ x : Grid n, a x • Pi.single x 1) =
    ∑ x : Grid n, a x • gridStep n (Pi.single x 1) at hlin
  rw [← hlin]
  apply congrArg (gridStep n)
  funext y
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]

theorem inner_gridStep (n : ℕ) (a : Grid n → ℝ) (f : CircleL2) :
    inner ℂ (gridStep n a) f = ∑ x : Grid n, (a x : ℂ) * inner ℂ (gridStep n (Pi.single x 1)) f := by
  rw [gridStep_cell_expansion, sum_inner]
  apply sum_congr rfl
  intro x hx
  change inner ℂ ((a x : ℂ) • gridStep n (Pi.single x 1)) f = _
  rw [inner_smul_left, Complex.conj_ofReal]

theorem localFactor_real_covariance_energy (n : ℕ) (a : Grid n → ℝ) (ha : ∀ x, 0 < a x)
    (z : Grid n → ℝ) :
    (∑ j : Option (DetailIndex n), (∑ x : Grid n, localFactor n a x j * z x) ^ 2) =
      ∑ x : Grid n, a x * (z x) ^ 2 := by
  change vectorSq ((localFactor n a)ᵀ *ᵥ z) = _
  rw [covariance_energy, localFactor_covariance n a ha]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply sum_congr rfl
  intro x hx
  ring

theorem localFactor_complex_covariance_energy (n : ℕ) (a : Grid n → ℝ) (ha : ∀ x, 0 < a x)
    (z : Grid n → ℂ) :
    (∑ j : Option (DetailIndex n), ‖∑ x : Grid n, (localFactor n a x j : ℂ) * z x‖ ^ 2) =
      ∑ x : Grid n, a x * ‖z x‖ ^ 2 := by
  have hr := localFactor_real_covariance_energy n a ha (fun x => (z x).re)
  have hi := localFactor_real_covariance_energy n a ha (fun x => (z x).im)
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  simp only [← pow_two]
  rw [sum_add_distrib, hr, hi, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  ring

def physicalFactorColumn (n : ℕ) (a : Grid n → ℝ) (j : Option (DetailIndex n)) : CircleL2 :=
  gridStep n (fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * localFactor n a x j)

theorem inner_physicalFactorColumn (n : ℕ) (a : Grid n → ℝ) (j : Option (DetailIndex n))
    (f : CircleL2) :
    inner ℂ (physicalFactorColumn n a j) f =
      ∑ x : Grid n, (localFactor n a x j : ℂ) * inner ℂ (normalizedCell n x) f := by
  rw [physicalFactorColumn, inner_gridStep]
  apply sum_congr rfl
  intro x hx
  rw [normalizedCell, inner_smul_left, Complex.conj_ofReal]
  push_cast
  ring

/-- Exact physical finite covariance energy for arbitrary complex circle
`L²` tests, using the genuine normalized dyadic cell family. -/
theorem physicalFactorColumn_covariance_energy (n : ℕ) (a : Grid n → ℝ)
    (ha : ∀ x, 0 < a x) (f : CircleL2) :
    (∑ j : Option (DetailIndex n), ‖inner ℂ (physicalFactorColumn n a j) f‖ ^ 2) =
      ∑ x : Grid n, a x * ‖inner ℂ (normalizedCell n x) f‖ ^ 2 := by
  simp_rw [inner_physicalFactorColumn]
  exact localFactor_complex_covariance_energy n a ha _

theorem physicalFactorColumn_bessel (n : ℕ) (a : Grid n → ℝ)
    (ha : ∀ x, 0 < a x) (U : ℝ) (hU : 0 ≤ U) (haU : ∀ x, a x ≤ U) (f : CircleL2) :
    (∑ j : Option (DetailIndex n), ‖inner ℂ (physicalFactorColumn n a j) f‖ ^ 2) ≤ U * ‖f‖ ^ 2 := by
  rw [physicalFactorColumn_covariance_energy n a ha]
  calc
    _ ≤ ∑ x : Grid n, U * ‖inner ℂ (normalizedCell n x) f‖ ^ 2 :=
      sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (haU x) (sq_nonneg _))
    _ = U * ∑ x : Grid n, ‖inner ℂ (normalizedCell n x) f‖ ^ 2 := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left ((normalizedCell_orthonormal n).sum_inner_products_le f) hU

theorem node_energy_sum_le (n : ℕ) (F : Option (DetailIndex n) → ℝ)
    (hF : ∀ j, 0 ≤ F j) (s : Finset HaarNode) :
    (∑ q ∈ s, if hq : nodeDepth q ≤ n then F (nodeMode n q hq) else 0) ≤ ∑ j, F j := by
  classical
  let a : HaarNode → ℝ := fun q => if hq : nodeDepth q ≤ n then F (nodeMode n q hq) else 0
  let h := s.filter (fun q => nodeDepth q ≤ n)
  have he : (∑ q ∈ s, a q) = ∑ q ∈ h, a q := by
    symm
    apply sum_subset (filter_subset _ _)
    intro q hq hnot
    have hn : ¬ nodeDepth q ≤ n := by simpa only [mem_filter, hq, true_and] using hnot
    simp [a, hn]
  change (∑ q ∈ s, a q) ≤ _
  rw [he]
  let e : HaarNode → Option (DetailIndex n) := fun q =>
    if hq : nodeDepth q ≤ n then nodeMode n q hq else none
  have hinj : Set.InjOn e (↑h : Set HaarNode) := by
    intro q hq r hr heq
    have hq' := (mem_filter.mp hq).2
    have hr' := (mem_filter.mp hr).2
    have he' := congrArg (modePath n) heq
    simpa only [e, dite_eq_left hq', dite_eq_left hr', modePath_nodeMode] using he'
  calc
    _ = ∑ q ∈ h, F (e q) := by
      apply sum_congr rfl
      intro q hq
      simp only [a, e, dite_eq_left (mem_filter.mp hq).2]
    _ = ∑ j ∈ h.image e, F j := by rw [sum_image]; exact hinj
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hF j)

/-- The actual countable physical factor family is Bessel. This is an
operator bound derived from finite covariance and genuine coefficient
convergence, rather than a stipulated frame assumption. -/
theorem globalHaarColumn_bessel_of_grid_approximation
    (c : ∀ N, Grid N → ℝ) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ N x, m ≤ c N x ∧ c N x ≤ U)
    (hcf : Filter.Tendsto (fun N => gridStep N (c N)) Filter.atTop (nhds f)) (v : CircleL2) :
    Summable (fun q : HaarNode => ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2) ∧
      (∑' q : HaarNode, ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2) ≤ U * ‖v‖ ^ 2 := by
  have hU : 0 ≤ U := (hm.trans_le (hc 0 ()).1).le.trans (hc 0 ()).2
  have hfinite (s : Finset HaarNode) :
      (∑ q ∈ s, ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2) ≤ U * ‖v‖ ^ 2 := by
    have hlim : Filter.Tendsto
        (fun N => ∑ q ∈ s, ‖inner ℂ (globalHaarColumn q (gridStep N (c N))) v‖ ^ 2)
        Filter.atTop (nhds (∑ q ∈ s, ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro q hq
      have hcol := globalHaarColumn_tendsto q (fun N => gridStep N (c N)) f m U hm
        (fun N => gridStep_bounds_ae N (c N) m U (hc N)) hcf
      exact (hcol.inner tendsto_const_nhds).norm.pow 2
    apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (s.sup nodeDepth)] with N hN
    have hqN (q : HaarNode) (hq : q ∈ s) : nodeDepth q ≤ N := (Finset.le_sup hq).trans hN
    calc
      _ = ∑ q ∈ s, if hq : nodeDepth q ≤ N then
          ‖inner ℂ (physicalFactorColumn N (c N) (nodeMode N q hq)) v‖ ^ 2 else 0 := by
        apply sum_congr rfl
        intro q hq
        rw [dite_eq_left (hqN q hq), globalHaarColumn_gridStep N q (hqN q hq)
          (c N) (fun x => hm.trans_le (hc N x).1)]
        rfl
      _ ≤ ∑ j, ‖inner ℂ (physicalFactorColumn N (c N) j) v‖ ^ 2 :=
        node_energy_sum_le N
          (fun j : Option (DetailIndex N) => ‖inner ℂ (physicalFactorColumn N (c N) j) v‖ ^ 2)
          (fun _ => sq_nonneg _) s
      _ ≤ _ := physicalFactorColumn_bessel N (c N) (fun x => hm.trans_le (hc N x).1)
        U hU (fun x => (hc N x).2) v
  have hs : Summable (fun q : HaarNode => ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs, Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite⟩

theorem globalHaarColumn_bessel (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    Summable (fun q : HaarNode => ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2) ∧
      (∑' q : HaarNode, ‖inner ℂ (globalHaarColumn q f) v‖ ^ 2) ≤ U * ‖v‖ ^ 2 := by
  exact globalHaarColumn_bessel_of_grid_approximation (fun N => localAverage N f) f m U hm
    (fun N x => localAverage_bounds_ae N f m U hfbound x)
    (DyadicApproximation.average_tendsto_of_real f hfreal) v

theorem gridStep_reference_expansion (n : ℕ) (b : Grid n → ℝ) :
    gridStep n b = ∑ i : Option (DetailIndex n),
      ((Real.sqrt (((2 ^ n : ℕ) : ℝ)))⁻¹ * ((haarMatrix n (fun _ => 1))ᵀ *ᵥ b) i) • ordinaryColumn n i := by
  rw [← referenceSynthesis_sum_columns]
  unfold referenceSynthesis gridStep
  apply congrArg (stepLp (2 ^ n))
  funext j
  have hs : Real.sqrt (((2 ^ n : ℕ) : ℝ)) ≠ 0 := by positivity
  change b ((gridCellEquiv n).symm j) = Real.sqrt _ *
    (haarMatrix n (fun _ => 1) *ᵥ ((Real.sqrt (((2 ^ n : ℕ) : ℝ)))⁻¹ •
      ((haarMatrix n (fun _ => 1))ᵀ *ᵥ b))) ((gridCellEquiv n).symm j)
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, referenceHaar_coorthogonal, Matrix.one_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem ordinaryColumn_lift (n r : ℕ) (i : Option (DetailIndex n)) :
    ordinaryColumn (n + r) (modeLift n r i) = ordinaryColumn n i := by
  induction r with
  | zero => rfl
  | succ r ih => exact (ordinaryColumn_refine (n + r) _).trans ih

theorem detailPath_level (n : ℕ) (i : DetailIndex n) :
    (detailPath n i).length + 1 = detailLevel n i := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i)
    · rfl
    · simpa only [detailPath, List.length_cons, detailLevel] using congrArg (fun k => k + 1) (ih i)
    · simpa only [detailPath, List.length_cons, detailLevel] using congrArg (fun k => k + 1) (ih i)

theorem nodeDepth_modePath (n : ℕ) (i : Option (DetailIndex n)) :
    nodeDepth (modePath n i) = modeLevel n i := by
  cases i with
  | none => rfl
  | some i => exact detailPath_level n i

theorem modeLevel_lift (n r : ℕ) (i : Option (DetailIndex n)) :
    modeLevel (n + r) (modeLift n r i) = modeLevel n i := by
  rw [← nodeDepth_modePath, modePath_lift, nodeDepth_modePath]

theorem inner_ordinary_physicalFactorColumn (n : ℕ) (a : Grid n → ℝ)
    (i j : Option (DetailIndex n)) :
    inner ℂ (ordinaryColumn n i) (physicalFactorColumn n a j) = (referenceFactor n a i j : ℂ) := by
  change inner ℂ (gridStep n (fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (fun _ => 1) i x))
    (gridStep n (fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * localFactor n a x j)) = _
  rw [gridStep_inner_complex]
  have hN : (0 : ℝ) < (((2 ^ n : ℕ) : ℝ)) := by positivity
  have hsum : (∑ x : Grid n, (Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (fun _ => 1) i x) *
      (Real.sqrt (((2 ^ n : ℕ) : ℝ)) * localFactor n a x j)) =
      (((2 ^ n : ℕ) : ℝ)) * ∑ x, haarColumn n (fun _ => 1) i x * localFactor n a x j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    calc
      _ = Real.sqrt (((2 ^ n : ℕ) : ℝ)) ^ 2 *
          (haarColumn n (fun _ => 1) i x * localFactor n a x j) := by ring
      _ = _ := by rw [Real.sq_sqrt hN.le]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
  rfl

theorem modeLevel_nodeMode (n : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n) :
    modeLevel n (nodeMode n q hq) = nodeDepth q := by
  rw [← nodeDepth_modePath, modePath_nodeMode]

theorem modeLevel_le_resolution (n : ℕ) (i : Option (DetailIndex n)) : modeLevel n i ≤ n := by
  cases i with
  | none => exact Nat.zero_le _
  | some i => exact detailLevel_le n i

theorem inner_real_smul (r : ℝ) (v w : CircleL2) :
    inner ℂ (r • v) w = (r : ℂ) * inner ℂ v w := by
  change inner ℂ ((r : ℂ) • v) w = _
  rw [inner_smul_left, Complex.conj_ofReal]

theorem physicalFactorColumn_coarse_zero (k r : ℕ) (a : Grid (k + r) → ℝ)
    (ha : ∀ x, 0 < a x) (j : Option (DetailIndex (k + r)))
    (hj : k < modeLevel (k + r) j) (b : Grid k → ℝ) :
    inner ℂ (gridStep k b) (physicalFactorColumn (k + r) a j) = 0 := by
  rw [gridStep_reference_expansion, sum_inner]
  apply sum_eq_zero
  intro i hi
  rw [inner_real_smul, ← ordinaryColumn_lift k r i, inner_ordinary_physicalFactorColumn]
  have hlevel : modeLevel (k + r) (modeLift k r i) < modeLevel (k + r) j := by
    rw [modeLevel_lift]
    exact (modeLevel_le_resolution k i).trans_lt hj
  rw [referenceFactor_finer_zero (k + r) a ha _ j hlevel, Complex.ofReal_zero, mul_zero]

/-- A fine weighted input column has zero pairing with every genuine
coarser step test, also for arbitrary measurable coefficients. -/
theorem globalHaarColumn_coarse_zero (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (k : ℕ) (b : Grid k → ℝ) (q : HaarNode) (hq : k < nodeDepth q) :
    inner ℂ (gridStep k b) (globalHaarColumn q f) = 0 := by
  let c : ∀ N, Grid N → ℝ := fun N => localAverage N f
  have hc (N : ℕ) (x : Grid N) : m ≤ c N x ∧ c N x ≤ U :=
    localAverage_bounds_ae N f m U hfbound x
  have hlim := globalHaarColumn_tendsto q (fun N => gridStep N (c N)) f m U hm
    (fun N => gridStep_bounds_ae N (c N) m U (hc N))
    (DyadicApproximation.average_tendsto_of_real f hfreal)
  have hinner : Filter.Tendsto
      (fun N => inner ℂ (gridStep k b) (globalHaarColumn q (gridStep N (c N))))
      Filter.atTop (nhds (inner ℂ (gridStep k b) (globalHaarColumn q f))) :=
    tendsto_const_nhds.inner hlim
  apply tendsto_nhds_unique hinner
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (max k (nodeDepth q))] with N hN
  have hkN : k ≤ N := (le_max_left _ _).trans hN
  have hqN : nodeDepth q ≤ N := (le_max_right _ _).trans hN
  rw [globalHaarColumn_gridStep N q hqN (c N) (fun x => hm.trans_le (hc N x).1)]
  change 0 = inner ℂ (gridStep k b) (physicalFactorColumn N (c N) (nodeMode N q hqN))
  symm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkN
  exact physicalFactorColumn_coarse_zero k r (c (k + r))
    (fun x => hm.trans_le (hc (k + r) x).1) _ (by rw [modeLevel_nodeMode]; exact hq) b

def nodesBelow (n : ℕ) : Finset HaarNode := univ.image (modePath n)

@[simp] theorem mem_nodesBelow (n : ℕ) (q : HaarNode) : q ∈ nodesBelow n ↔ nodeDepth q ≤ n := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    exact modePath_depth n i
  · intro h
    obtain ⟨i, hi⟩ := modePath_surjective_below n q h
    exact mem_image.mpr ⟨i, mem_univ _, hi⟩

theorem nodesBelow_mono {k n : ℕ} (hkn : k ≤ n) : nodesBelow k ⊆ nodesBelow n := by
  intro q hq
  exact (mem_nodesBelow n q).mpr (((mem_nodesBelow k q).mp hq).trans hkn)

@[simp] theorem nodeMode_modePath (n : ℕ) (i : Option (DetailIndex n))
    (hi : nodeDepth (modePath n i) ≤ n) : nodeMode n (modePath n i) hi = i := by
  apply modePath_injective n
  exact modePath_nodeMode n _ hi

theorem sum_nodesBelow (n : ℕ) (F : Option (DetailIndex n) → ℝ) :
    (∑ q ∈ nodesBelow n, if hq : nodeDepth q ≤ n then F (nodeMode n q hq) else 0) = ∑ j, F j := by
  rw [nodesBelow, sum_image]
  · apply sum_congr rfl
    intro i hi
    rw [dite_eq_left (modePath_depth n i), nodeMode_modePath]
  · exact (modePath_injective n).injOn

theorem normalizedCell_gridStep_inner_sq (n : ℕ) (x : Grid n) (b : Grid n → ℝ) :
    ‖inner ℂ (normalizedCell n x) (gridStep n b)‖ ^ 2 =
      (((2 ^ n : ℕ) : ℝ))⁻¹ * (b x) ^ 2 := by
  rw [normalizedCell, inner_smul_left, Complex.conj_ofReal, gridStep_inner_complex]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (((2 ^ n : ℕ) : ℝ)))]
  have hN : (((2 ^ n : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem physicalFactorColumn_step_covariance_energy (n : ℕ) (a : Grid n → ℝ)
    (ha : ∀ x, 0 < a x) (b : Grid n → ℝ) :
    (∑ j : Option (DetailIndex n), ‖inner ℂ (physicalFactorColumn n a j) (gridStep n b)‖ ^ 2) =
      (inner ℂ (gridStep n a) (gridStep n (fun x => (b x) ^ 2))).re := by
  rw [physicalFactorColumn_covariance_energy n a ha, gridStep_inner]
  simp_rw [normalizedCell_gridStep_inner_sq]
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  ring

theorem physicalFactorColumn_coarse_covariance_energy (k r : ℕ) (a : Grid (k + r) → ℝ)
    (ha : ∀ x, 0 < a x) (b : Grid k → ℝ) :
    (∑ j : Option (DetailIndex (k + r)), ‖inner ℂ (physicalFactorColumn (k + r) a j) (gridStep k b)‖ ^ 2) =
      (inner ℂ (gridStep (k + r) a) (gridStep k (fun x => (b x) ^ 2))).re := by
  calc
    _ = (inner ℂ (gridStep (k + r) a)
        (gridStep (k + r) (fun y => (b (ancestorLeaf k r y)) ^ 2))).re := by
      rw [← gridStep_ancestor k r b]
      exact physicalFactorColumn_step_covariance_energy (k + r) a ha _
    _ = _ := by rw [gridStep_ancestor k r (fun x => (b x) ^ 2)]

theorem globalHaarColumn_step_covariance_energy (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (k : ℕ) (b : Grid k → ℝ) :
    (∑' q : HaarNode, ‖inner ℂ (globalHaarColumn q f) (gridStep k b)‖ ^ 2) =
      (inner ℂ f (gridStep k (fun x => (b x) ^ 2))).re := by
  let c : ∀ N, Grid N → ℝ := fun N => localAverage N f
  have hc (N : ℕ) (x : Grid N) : m ≤ c N x ∧ c N x ≤ U :=
    localAverage_bounds_ae N f m U hfbound x
  have hcf : Filter.Tendsto (fun N => gridStep N (c N)) Filter.atTop (nhds f) :=
    DyadicApproximation.average_tendsto_of_real f hfreal
  have htrunc : (∑' q : HaarNode, ‖inner ℂ (globalHaarColumn q f) (gridStep k b)‖ ^ 2) =
      ∑ q ∈ nodesBelow k, ‖inner ℂ (globalHaarColumn q f) (gridStep k b)‖ ^ 2 := by
    apply tsum_eq_sum
    intro q hq
    have hdepth : k < nodeDepth q := by simpa only [mem_nodesBelow, not_le] using hq
    rw [inner_eq_zero_symm.mp (globalHaarColumn_coarse_zero f m U hm hfreal hfbound k b q hdepth)]
    simp
  rw [htrunc]
  have hlim : Filter.Tendsto
      (fun N => ∑ q ∈ nodesBelow k, ‖inner ℂ (globalHaarColumn q (gridStep N (c N))) (gridStep k b)‖ ^ 2)
      Filter.atTop (nhds (∑ q ∈ nodesBelow k, ‖inner ℂ (globalHaarColumn q f) (gridStep k b)‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro q hq
    have hcol := globalHaarColumn_tendsto q (fun N => gridStep N (c N)) f m U hm
      (fun N => gridStep_bounds_ae N (c N) m U (hc N)) hcf
    exact (hcol.inner tendsto_const_nhds).norm.pow 2
  have hrhs : Filter.Tendsto
      (fun N => (inner ℂ (gridStep N (c N)) (gridStep k (fun x => (b x) ^ 2))).re)
      Filter.atTop (nhds ((inner ℂ f (gridStep k (fun x => (b x) ^ 2))).re)) := by
    have hh : Filter.Tendsto
        (fun N => inner ℂ (gridStep N (c N)) (gridStep k (fun x => (b x) ^ 2)))
        Filter.atTop (nhds (inner ℂ f (gridStep k (fun x => (b x) ^ 2)))) :=
      hcf.inner tendsto_const_nhds
    exact (Complex.continuous_re.tendsto _).comp hh
  apply tendsto_nhds_unique hlim
  apply hrhs.congr'
  filter_upwards [Filter.eventually_ge_atTop k] with N hkN
  let F : Option (DetailIndex N) → ℝ := fun j => ‖inner ℂ (physicalFactorColumn N (c N) j) (gridStep k b)‖ ^ 2
  let G : HaarNode → ℝ := fun q => if hq : nodeDepth q ≤ N then F (nodeMode N q hq) else 0
  have hsum : (∑ q ∈ nodesBelow k, G q) = ∑ j, F j := by
    calc
      _ = ∑ q ∈ nodesBelow N, G q := by
        apply sum_subset (nodesBelow_mono hkN)
        intro q hqN hqk
        have hqN' : nodeDepth q ≤ N := (mem_nodesBelow N q).mp hqN
        have hqk' : k < nodeDepth q := by simpa only [mem_nodesBelow, not_le] using hqk
        dsimp only [G]
        rw [dite_eq_left hqN']
        dsimp only [F]
        have hzero : inner ℂ (gridStep k b) (physicalFactorColumn N (c N) (nodeMode N q hqN')) = 0 := by
          obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkN
          exact physicalFactorColumn_coarse_zero k r (c (k + r))
            (fun x => hm.trans_le (hc (k + r) x).1) _ (by rw [modeLevel_nodeMode]; exact hqk') b
        rw [inner_eq_zero_symm.mp hzero]
        simp
      _ = _ := sum_nodesBelow N F
  have heq : (∑ q ∈ nodesBelow k,
      ‖inner ℂ (globalHaarColumn q (gridStep N (c N))) (gridStep k b)‖ ^ 2) = ∑ j, F j := by
    rw [← hsum]
    apply sum_congr rfl
    intro q hq
    have hqN : nodeDepth q ≤ N := ((mem_nodesBelow k q).mp hq).trans hkN
    dsimp only [G]
    rw [dite_eq_left hqN,
      globalHaarColumn_gridStep N q hqN (c N) (fun x => hm.trans_le (hc N x).1)]
    rfl
  rw [heq]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkN
  exact (physicalFactorColumn_coarse_covariance_energy k r (c (k + r))
    (fun x => hm.trans_le (hc (k + r) x).1) b).symm

theorem globalHaarColumn_real_ae (q : HaarNode) (f : CircleL2)
    (hf : ∀ᵐ y ∂haarAddCircle, (f y).im = 0) :
    ∀ᵐ y ∂haarAddCircle, (globalHaarColumn q f y).im = 0 := by
  let n := nodeDepth q
  let i := nodeMode n q le_rfl
  let r : Grid n → ℝ := fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (localAverage n f) i x
  have hr (x : Grid n) : ∀ᵐ y ∂haarAddCircle, (r x • cellRestriction n x f : CircleL2) y =
      (r x : ℂ) * (cellSet n x).indicator f y := by
    filter_upwards [Lp.coeFn_smul (r x) (cellRestriction n x f), cellRestriction_ae n x f] with y ha hb
    rw [ha]
    change (r x : ℂ) * (cellRestriction n x f y) = _
    rw [hb]
  have hall : ∀ᵐ y ∂haarAddCircle, ∀ x : Grid n,
      (r x • cellRestriction n x f : CircleL2) y = (r x : ℂ) * (cellSet n x).indicator f y :=
    ae_all_iff.mpr hr
  have hsum := Lp.coeFn_fun_finsetSum univ (fun x : Grid n => r x • cellRestriction n x f)
  filter_upwards [hsum, hall, hf] with y hs ha hb
  change ((∑ x : Grid n, r x • cellRestriction n x f : CircleL2) y).im = 0
  rw [hs]
  simp only [Complex.im_sum]
  apply sum_eq_zero
  intro x hx
  rw [ha x]
  by_cases hy : y ∈ cellSet n x
  · simp [Set.indicator_of_mem hy, Complex.mul_im, hb]
  · simp [Set.indicator_of_notMem hy]

theorem inner_real_fields_im (f g : CircleL2)
    (hf : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hg : ∀ᵐ y ∂haarAddCircle, (g y).im = 0) : (inner ℂ f g).im = 0 := by
  have hi := integral_im (L2.integrable_inner (𝕜 := ℂ) f g)
  rw [← L2.inner_def] at hi
  change RCLike.im (inner ℂ f g) = 0
  rw [← hi]
  apply integral_eq_zero_of_ae
  filter_upwards [hf, hg] with y ha hb
  simp [RCLike.inner_apply, ha, hb]

theorem gridStep_real_ae (n : ℕ) (a : Grid n → ℝ) :
    ∀ᵐ y ∂haarAddCircle, (gridStep n a y).im = 0 := by
  filter_upwards [gridStep_ae_cellIndex n a] with y hy
  simp [hy]

theorem inner_globalHaarColumn_gridStep_im (q : HaarNode) (f : CircleL2)
    (hf : ∀ᵐ y ∂haarAddCircle, (f y).im = 0) (n : ℕ) (a : Grid n → ℝ) :
    (inner ℂ (globalHaarColumn q f) (gridStep n a)).im = 0 :=
  inner_real_fields_im _ _ (globalHaarColumn_real_ae q f hf) (gridStep_real_ae n a)

theorem complex_real_pair_norm_sq (z w : ℂ) (hz : z.im = 0) (hw : w.im = 0) :
    ‖z + Complex.I * w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, hz, hw]
  ring

theorem globalHaarColumn_complexStep_covariance_energy (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (k : ℕ) (a b : Grid k → ℝ) :
    (∑' q : HaarNode, ‖inner ℂ (globalHaarColumn q f) (DyadicApproximation.complexGridStep k a b)‖ ^ 2) =
      (inner ℂ f (gridStep k (fun x => (a x) ^ 2 + (b x) ^ 2))).re := by
  have hterm (q : HaarNode) :
      ‖inner ℂ (globalHaarColumn q f) (DyadicApproximation.complexGridStep k a b)‖ ^ 2 =
        ‖inner ℂ (globalHaarColumn q f) (gridStep k a)‖ ^ 2 +
        ‖inner ℂ (globalHaarColumn q f) (gridStep k b)‖ ^ 2 := by
    rw [DyadicApproximation.complexGridStep, inner_add_right, inner_smul_right]
    exact complex_real_pair_norm_sq _ _ (inner_globalHaarColumn_gridStep_im q f hfreal k a)
      (inner_globalHaarColumn_gridStep_im q f hfreal k b)
  simp_rw [hterm]
  rw [Summable.tsum_add (globalHaarColumn_bessel f m U hm hfreal hfbound (gridStep k a)).1
    (globalHaarColumn_bessel f m U hm hfreal hfbound (gridStep k b)).1,
    globalHaarColumn_step_covariance_energy f m U hm hfreal hfbound k a,
    globalHaarColumn_step_covariance_energy f m U hm hfreal hfbound k b]
  rw [show (fun x => (a x) ^ 2 + (b x) ^ 2) = (fun x => (a x) ^ 2) + (fun x => (b x) ^ 2) from rfl,
    gridStep_add, inner_add_right, Complex.add_re]

end SHE.FiniteHaar
