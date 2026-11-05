module

public import SHE.HaarOperator

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar

open Finset Matrix MeasureTheory AddCircle CircleHeat FiniteTransport
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem referenceFactor_vectorSq_lower (n : ℕ) (a : Grid n → ℝ) (m : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x) (z : Option (DetailIndex n) → ℝ) :
    m * vectorSq z ≤ vectorSq (referenceFactor n a *ᵥ z) := by
  have hp : ∀ x, 0 < a x := fun x => hm.trans_le (ha x)
  have ht := referenceFactor_lower n a hp
  have hd := referenceFactor_diag_pos n a hp
  have hdet : IsUnit (referenceFactor n a).det := isUnit_iff_ne_zero.mpr
    ((ht.det_ne_zero_iff).mpr (fun i => (hd i).ne'))
  let : Invertible (referenceFactor n a) := Matrix.invertibleOfIsUnitDet _ hdet
  exact factor_lower_of_covariance _ m hm (referenceFactor_covariance_lower n a hp m ha) z

theorem physicalFactorColumn_reference (n : ℕ) (a : Grid n → ℝ) (j : Option (DetailIndex n)) :
    physicalFactorColumn n a j = referenceSynthesis n (fun i => referenceFactor n a i j) := by
  have hmat : haarMatrix n (fun _ => 1) * referenceFactor n a = localFactor n a := by
    rw [referenceFactor, ← Matrix.mul_assoc, referenceHaar_coorthogonal, Matrix.one_mul]
  unfold physicalFactorColumn referenceSynthesis gridStep
  apply congrArg (stepLp (2 ^ n))
  funext x
  apply congrArg (fun r : ℝ => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * r)
  exact (congrArg (fun A => A ((gridCellEquiv n).symm x) j) hmat).symm

theorem physicalFactorColumn_real_synthesis (n : ℕ) (a : Grid n → ℝ)
    (z : Option (DetailIndex n) → ℝ) :
    (∑ j, z j • physicalFactorColumn n a j) = referenceSynthesis n (referenceFactor n a *ᵥ z) := by
  simp_rw [physicalFactorColumn_reference]
  have hlin := map_sum (referenceSynthesisLinear n)
    (fun j : Option (DetailIndex n) => z j • (fun i => referenceFactor n a i j)) univ
  simp only [map_smul] at hlin
  change referenceSynthesis n (∑ j, z j • (fun i => referenceFactor n a i j)) =
    ∑ j, z j • referenceSynthesis n (fun i => referenceFactor n a i j) at hlin
  rw [← hlin]
  apply congrArg (referenceSynthesis n)
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  apply sum_congr rfl
  intro j hj
  ring

theorem physicalFactorColumn_real_riesz (n : ℕ) (a : Grid n → ℝ) (m : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x) (z : Option (DetailIndex n) → ℝ) :
    m * ∑ j, (z j) ^ 2 ≤ ‖∑ j, z j • physicalFactorColumn n a j‖ ^ 2 := by
  rw [physicalFactorColumn_real_synthesis, referenceSynthesis_norm_sq]
  exact referenceFactor_vectorSq_lower n a m hm ha z

theorem ordinaryColumn_orthonormal (n : ℕ) : Orthonormal ℂ (ordinaryColumn n) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hp : physicalFactorColumn n (fun _ => 1) j = ordinaryColumn n j := by
    unfold physicalFactorColumn ordinaryColumn gridStep normalizedColumn
    apply congrArg (stepLp (2 ^ n))
    funext x
    simp only [localFactor_apply, one_mul]
  rw [← hp, inner_ordinary_physicalFactorColumn, referenceFactor, localFactor_one, referenceHaar_orthogonal]
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem ordinaryColumn_complex_synthesis_norm_sq (n : ℕ) (z : Option (DetailIndex n) → ℂ) :
    ‖∑ j, z j • ordinaryColumn n j‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
  have hh := congrArg Complex.re ((ordinaryColumn_orthonormal n).inner_sum z z univ)
  have hterm (j : Option (DetailIndex n)) : ((starRingEnd ℂ) (z j) * z j).re = ‖z j‖ ^ 2 := by
    rw [← RCLike.inner_apply']
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (z j)).symm
  have hl : (inner ℂ (∑ j, z j • ordinaryColumn n j) (∑ j, z j • ordinaryColumn n j)).re =
      ‖∑ j, z j • ordinaryColumn n j‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  simpa only [hl, Complex.re_sum, hterm] using hh

theorem physicalFactorColumn_complex_synthesis (n : ℕ) (a : Grid n → ℝ)
    (z : Option (DetailIndex n) → ℂ) :
    (∑ j, z j • physicalFactorColumn n a j) =
      ∑ i, (∑ j, (referenceFactor n a i j : ℂ) * z j) • ordinaryColumn n i := by
  simp_rw [physicalFactorColumn_reference, referenceSynthesis_sum_columns, Finset.smul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_smul]
  apply sum_congr rfl
  intro j hj
  change z j • ((referenceFactor n a i j : ℂ) • ordinaryColumn n i) = _
  rw [smul_smul, mul_comm]

theorem referenceFactor_complex_lower (n : ℕ) (a : Grid n → ℝ) (m : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x) (z : Option (DetailIndex n) → ℂ) :
    m * ∑ j, ‖z j‖ ^ 2 ≤ ∑ i, ‖∑ j, (referenceFactor n a i j : ℂ) * z j‖ ^ 2 := by
  have hr := referenceFactor_vectorSq_lower n a m hm ha (fun j => (z j).re)
  have hi := referenceFactor_vectorSq_lower n a m hm ha (fun j => (z j).im)
  simp only [vectorSq, Matrix.mulVec, dotProduct] at hr hi
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  simp only [← pow_two]
  rw [sum_add_distrib, sum_add_distrib, mul_add]
  exact add_le_add hr hi

theorem physicalFactorColumn_complex_riesz (n : ℕ) (a : Grid n → ℝ) (m : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x) (z : Option (DetailIndex n) → ℂ) :
    m * ∑ j, ‖z j‖ ^ 2 ≤ ‖∑ j, z j • physicalFactorColumn n a j‖ ^ 2 := by
  rw [physicalFactorColumn_complex_synthesis, ordinaryColumn_complex_synthesis_norm_sq]
  exact referenceFactor_complex_lower n a m hm ha z

theorem sum_extend_zero {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (e : α → β) (he : Function.Injective e) (z : α → ℂ) (F : β → ℂ → M)
    (hF : ∀ j, F j 0 = 0) :
    (∑ j : β, F j (Function.extend e z (fun _ => 0) j)) = ∑ i : α, F (e i) (z i) := by
  classical
  calc
    _ = ∑ j ∈ univ.image e, F j (Function.extend e z (fun _ => 0) j) := by
      symm
      apply sum_subset (subset_univ _)
      intro j hj hnot
      have hn : ¬ ∃ i, e i = j := by
        intro hh
        obtain ⟨i, rfl⟩ := hh
        exact hnot (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
      rw [Function.extend_apply' _ _ j hn, hF]
    _ = _ := by
      rw [sum_image]
      · apply sum_congr rfl
        intro i hi
        rw [he.extend_apply]
      · exact he.injOn

theorem modeLift_injective (n r : ℕ) : Function.Injective (modeLift n r) := by
  intro i j h
  apply modePath_injective n
  have hh := congrArg (modePath (n + r)) h
  simpa only [modePath_lift] using hh

theorem physicalFactorColumn_prefix_complex_riesz (k r : ℕ) (a : Grid (k + r) → ℝ)
    (m : ℝ) (hm : 0 < m) (ha : ∀ x, m ≤ a x) (z : Option (DetailIndex k) → ℂ) :
    m * ∑ j, ‖z j‖ ^ 2 ≤
      ‖∑ j, z j • physicalFactorColumn (k + r) a (modeLift k r j)‖ ^ 2 := by
  let e := modeLift k r
  let w := Function.extend e z (fun _ => 0)
  have hnorm : (∑ j : Option (DetailIndex (k + r)), ‖w j‖ ^ 2) = ∑ i, ‖z i‖ ^ 2 :=
    sum_extend_zero e (modeLift_injective k r) z (fun _ z => ‖z‖ ^ 2) (by simp)
  have hsum : (∑ j : Option (DetailIndex (k + r)), w j • physicalFactorColumn (k + r) a j) =
      ∑ i, z i • physicalFactorColumn (k + r) a (e i) :=
    sum_extend_zero e (modeLift_injective k r) z (fun j z => z • physicalFactorColumn (k + r) a j) (by simp)
  have hh := physicalFactorColumn_complex_riesz (k + r) a m hm ha w
  rw [hnorm, hsum] at hh
  exact hh

theorem globalHaarColumn_prefix_complex_riesz (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (k : ℕ) (z : Option (DetailIndex k) → ℂ) :
    m * ∑ j, ‖z j‖ ^ 2 ≤ ‖∑ j, z j • globalHaarColumn (modePath k j) f‖ ^ 2 := by
  let c : ∀ N, Grid N → ℝ := fun N => localAverage N f
  have hc (N : ℕ) (x : Grid N) : m ≤ c N x ∧ c N x ≤ U :=
    localAverage_bounds_ae N f m U hfbound x
  have hshift : Filter.Tendsto (fun r : ℕ => k + r) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with r hr
    omega
  have hcf : Filter.Tendsto (fun r => gridStep (k + r) (c (k + r))) Filter.atTop (nhds f) :=
    (DyadicApproximation.average_tendsto_of_real f hfreal).comp hshift
  have hcol (i : Option (DetailIndex k)) : Filter.Tendsto
      (fun r => physicalFactorColumn (k + r) (c (k + r)) (modeLift k r i))
      Filter.atTop (nhds (globalHaarColumn (modePath k i) f)) := by
    have hg := globalHaarColumn_tendsto (modePath k i)
      (fun r => gridStep (k + r) (c (k + r))) f m U hm
      (fun r => gridStep_bounds_ae _ _ m U (hc (k + r))) hcf
    apply hg.congr'
    apply Filter.Eventually.of_forall
    intro r
    change globalHaarColumn (modePath k i) (gridStep (k + r) (c (k + r))) =
      physicalFactorColumn (k + r) (c (k + r)) (modeLift k r i)
    have hdepth : nodeDepth (modePath k i) ≤ k + r := (modePath_depth k i).trans (Nat.le_add_right k r)
    rw [globalHaarColumn_gridStep (k + r) _ hdepth (c (k + r))
      (fun x => hm.trans_le (hc (k + r) x).1)]
    have hid : nodeMode (k + r) (modePath k i) hdepth = modeLift k r i := by
      apply modePath_injective (k + r)
      simp
    rw [hid]
    rfl
  have hsum : Filter.Tendsto
      (fun r => ∑ j, z j • physicalFactorColumn (k + r) (c (k + r)) (modeLift k r j))
      Filter.atTop (nhds (∑ j, z j • globalHaarColumn (modePath k j) f)) :=
    tendsto_finsetSum univ (fun j _ => (hcol j).const_smul (z j))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hsum.norm.pow 2)
  exact Filter.Eventually.of_forall (fun r => physicalFactorColumn_prefix_complex_riesz k r (c (k + r))
    m hm (fun x => (hc (k + r) x).1) z)

theorem nodesBelow_tendsto : Filter.Tendsto nodesBelow Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro s
  filter_upwards [Filter.eventually_ge_atTop (s.sup nodeDepth)] with N hN
  intro q hq
  exact (mem_nodesBelow N q).mpr ((Finset.le_sup hq).trans hN)

theorem factor_single_value (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (q : HaarNode) (z : ℂ) :
    factor f m U hm hfreal hfbound (lp.single 2 q z) = z • globalHaarColumn q f := by
  have he : lp.single 2 q z = z • (lp.single 2 q (1 : ℂ) : HaarInput) := by
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : HaarNode => ℂ) 2 q z (1 : ℂ)
  rw [he, map_smul, factor_single]

/-- A true Riesz lower bound for the actual infinite physical synthesis.
This proves injectivity in addition to the operator covariance. -/
theorem factor_norm_sq_lower (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (x : HaarInput) :
    m * ‖x‖ ^ 2 ≤ ‖factor f m U hm hfreal hfbound x‖ ^ 2 := by
  let P : ℕ → HaarInput := fun N => ∑ q ∈ nodesBelow N, lp.single 2 q (x q)
  have hp : Filter.Tendsto P Filter.atTop (nhds x) :=
    (lp.hasSum_single ENNReal.ofNat_ne_top x).comp nodesBelow_tendsto
  have henergy : Filter.Tendsto (fun N => ∑ q ∈ nodesBelow N, ‖x q‖ ^ 2)
      Filter.atTop (nhds (‖x‖ ^ 2)) := by
    have hh := (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) x).comp nodesBelow_tendsto
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using hh
  have hbound (N : ℕ) : m * (∑ q ∈ nodesBelow N, ‖x q‖ ^ 2) ≤
      ‖factor f m U hm hfreal hfbound (P N)‖ ^ 2 := by
    have hh := globalHaarColumn_prefix_complex_riesz f m U hm hfreal hfbound N (fun i => x (modePath N i))
    have he : (∑ q ∈ nodesBelow N, ‖x q‖ ^ 2) = ∑ i, ‖x (modePath N i)‖ ^ 2 := by
      rw [nodesBelow, sum_image]
      exact (modePath_injective N).injOn
    have hs : factor f m U hm hfreal hfbound (P N) =
        ∑ i, x (modePath N i) • globalHaarColumn (modePath N i) f := by
      simp only [P, map_sum, factor_single_value]
      rw [nodesBelow, sum_image]
      exact (modePath_injective N).injOn
    rw [he, hs]
    exact hh
  exact le_of_tendsto_of_tendsto (henergy.const_mul m)
    (((factor f m U hm hfreal hfbound).continuous.tendsto x |>.comp hp).norm.pow 2)
    (Filter.Eventually.of_forall hbound)

end SHE.FiniteHaar
