module

public import SHE.StoppedFourier
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section
set_option autoImplicit false

/-! Finite covariance frames from the proved physical separated-history correlation. -/
noncomputable section
namespace SHE.StoppedFourier
open Set MeasureTheory AddCircle
open scoped InnerProductSpace ENNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem finite_frame_of_inner_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (hn : 0 < n) (v : Fin n → E)
    (hcross : ∀ i j : Fin n, i ≠ j →
      |inner ℝ (v i) (v j)| ≤ (‖v i‖ ^ 2 + ‖v j‖ ^ 2) / (4 * n)) :
    (1 / 2 : ℝ) * ∑ i : Fin n, ‖v i‖ ^ 2 ≤ ‖∑ i : Fin n, v i‖ ^ 2 := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint : ∀ i j : Fin n,
      (if j = i then ‖v i‖ ^ 2 else 0) - (‖v i‖ ^ 2 + ‖v j‖ ^ 2) / (4 * n) ≤
        inner ℝ (v i) (v j) := by
    intro i j
    by_cases hij : j = i
    · subst j
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
      have he : 0 ≤ (‖v i‖ ^ 2 + ‖v i‖ ^ 2) / (4 * n) := by positivity
      linarith
    · rw [ite_eq_right hij]
      simpa only [zero_sub] using (abs_le.mp (hcross i j (Ne.symm hij))).1
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_hi : i ∈ Finset.univ) =>
    Finset.sum_le_sum (s := Finset.univ) (fun j (_hj : j ∈ Finset.univ) => hpoint i j))
  have hnorm : (∑ i : Fin n, ∑ j : Fin n, inner ℝ (v i) (v j)) = ‖∑ i : Fin n, v i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  rw [hnorm] at hsum
  have halg : (∑ i : Fin n, ∑ j : Fin n,
      ((if j = i then ‖v i‖ ^ 2 else 0) - (‖v i‖ ^ 2 + ‖v j‖ ^ 2) / (4 * n))) =
      (1 / 2 : ℝ) * ∑ i : Fin n, ‖v i‖ ^ 2 := by
    have hdiag : ∀ i : Fin n, (∑ j : Fin n, if j = i then ‖v i‖ ^ 2 else 0) = ‖v i‖ ^ 2 := by
      intro i
      simpa only using Fintype.sum_ite_eq' i (fun _j : Fin n => ‖v i‖ ^ 2)
    have hpen : (∑ i : Fin n, ∑ j : Fin n, (‖v i‖ ^ 2 + ‖v j‖ ^ 2) / (4 * n)) =
        (1 / 2 : ℝ) * ∑ i : Fin n, ‖v i‖ ^ 2 := by
      calc
        _ = (∑ i : Fin n, ∑ j : Fin n, (‖v i‖ ^ 2 + ‖v j‖ ^ 2)) / (4 * n) := by
          simp only [Finset.sum_div]
        _ = ((n : ℝ) * (∑ i : Fin n, ‖v i‖ ^ 2) + (n : ℝ) * (∑ i : Fin n, ‖v i‖ ^ 2)) / (4 * n) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
        _ = _ := by field_simp; ring
    simp only [Finset.sum_sub_distrib, hdiag, hpen]
    ring
  rwa [halg] at hsum

 theorem correlation_to_inner_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x y : E} {A N : ℝ} (hN : 0 < N) (hA : 4 * N ^ 2 + 1 ≤ A)
    (hpair : ‖inner ℂ x y‖ ^ 2 ≤ (A - 1)⁻¹ * ‖x‖ ^ 2 * ‖y‖ ^ 2) :
    |(inner ℂ x y).re| ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / (4 * N) := by
  have hA1 : 0 < A - 1 := by nlinarith
  have hpair' : (A - 1) * ‖inner ℂ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have he : (A - 1)⁻¹ * ‖x‖ ^ 2 * ‖y‖ ^ 2 = (‖x‖ ^ 2 * ‖y‖ ^ 2) / (A - 1) := by ring
    rw [he] at hpair
    simpa only [mul_comm] using (le_div_iff₀ hA1).mp hpair
  have hsmall : (4 * N ^ 2) * ‖inner ℂ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖inner ℂ x y‖]
  have hsq : (4 * N * ‖inner ℂ x y‖) ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ ^ 2 - ‖y‖ ^ 2)]
  have hnorm : ‖inner ℂ x y‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / (4 * N) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * N)).mpr
    have he := (sq_le_sq₀ (show 0 ≤ 4 * N * ‖inner ℂ x y‖ by positivity)
      (show 0 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 by positivity)).mp hsq
    nlinarith
  exact (Complex.abs_re_le_norm _).trans hnorm

 theorem finite_frame_of_correlation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {n : ℕ} (hn : 0 < n) (v : Fin n → E) {A : ℝ}
    (hA : 4 * (n : ℝ) ^ 2 + 1 ≤ A)
    (hcross : ∀ i j : Fin n, i ≠ j →
      ‖inner ℂ (v i) (v j)‖ ^ 2 ≤ (A - 1)⁻¹ * ‖v i‖ ^ 2 * ‖v j‖ ^ 2) :
    (1 / 2 : ℝ) * ∑ i : Fin n, ‖v i‖ ^ 2 ≤ ‖∑ i : Fin n, v i‖ ^ 2 := by
  let := InnerProductSpace.rclikeToReal ℂ E
  apply finite_frame_of_inner_bound hn v
  intro i j hij
  rw [real_inner_eq_re_inner ℂ]
  exact correlation_to_inner_bound (by exact_mod_cast hn) hA (hcross i j hij)

def historyTimeVector {ι : Type*} (I : Finset ι) (z : ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) (q : ℝ) :
    Lp CircleL2 2 (volume.restrict (Ici q)) :=
  (historyF_memLp_time I z σ target center hages q).toLp (historyF I z σ target center)

theorem historyTimeVector_norm_sq {ι : Type*} (I : Finset ι) (z : ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) (q : ℝ) :
    ‖historyTimeVector I z σ target center hages q‖ ^ 2 =
      (fullPhysicalEnergy (historyF I z σ target center) q).toReal :=
  historyF_time_norm_sq I z σ target center hages q

theorem toLp_finsetSum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {μ : Measure α} (I : Finset ι) (f : ι → α → E) (hf : ∀ i, MemLp (f i) 2 μ) :
    (memLp_finsetSum I (fun i _ => hf i)).toLp (fun x => ∑ i ∈ I, f i x) =
      ∑ i ∈ I, (hf i).toLp (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz : MemLp (0 : α → E) 2 μ := MemLp.zero
    have he : (fun _ : α => (0 : E)) =ᵐ[μ] (0 : α → E) :=
      Filter.Eventually.of_forall (fun _ => rfl)
    exact (MemLp.toLp_congr (memLp_finsetSum ∅ (fun i _ => hf i)) hz he).trans
      (MemLp.toLp_zero hz)
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    calc
      _ = (hf i).toLp (f i) +
          (memLp_finsetSum I (fun j _ => hf j)).toLp (fun x => ∑ j ∈ I, f j x) := by
        exact MemLp.toLp_add (hf i) (memLp_finsetSum I (fun j _ => hf j))
      _ = _ := by rw [ih]

theorem memLp_fullEnergy_norm_sq {H : ℝ → CircleL2} {q : ℝ}
    (hm : MemLp H 2 (volume.restrict (Ici q))) :
    (fullPhysicalEnergy H q).toReal = ‖hm.toLp H‖ ^ 2 := by
  rw [toLp_norm_sq_eq_integral]
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  unfold fullPhysicalEnergy
  simp_rw [circle_spatial_energy_eq_norm_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun u => sq_nonneg _)),
    ENNReal.toReal_ofReal (integral_nonneg (fun u => sq_nonneg _))]

/-- The all-age covariance frame for actual finite physical heat-history groups.
The assumptions express only stopping-age separation, not any Gram-matrix bound. -/
theorem separated_history_covariance_frame {ι : Type*} {n : ℕ} (hn : 0 < n)
    (I : Fin n → Finset ι) (z : Fin n → ι → ℂ) (σ target : Fin n → ι → ℝ)
    (center : Fin n → ι → HeatCircle) (hages : ∀ g, ∀ i ∈ I g, σ g i ≤ target g i)
    (lower upper : Fin n → ℝ) {q A : ℝ} (hA : 4 * (n : ℝ) ^ 2 + 1 ≤ A)
    (hlo : ∀ g, 0 < lower g) (hlohi : ∀ g, lower g ≤ upper g)
    (hstlo : ∀ g, ∀ i ∈ I g, q + lower g ≤ σ g i)
    (hsthi : ∀ g, ∀ i ∈ I g, σ g i ≤ q + upper g)
    (hsep : ∀ g h, g < h → A * upper g ≤ lower h) :
    (1 / 2 : ℝ) * (∑ g : Fin n, (fullPhysicalEnergy (historyF (I g) (z g) (σ g) (target g) (center g)) q).toReal) ≤
      (fullPhysicalEnergy (fun u => ∑ g : Fin n, historyF (I g) (z g) (σ g) (target g) (center g) u) q).toReal := by
  let H : Fin n → ℝ → CircleL2 := fun g => historyF (I g) (z g) (σ g) (target g) (center g)
  let v : Fin n → Lp CircleL2 2 (volume.restrict (Ici q)) :=
    fun g => historyTimeVector (I g) (z g) (σ g) (target g) (center g) (hages g) q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA1 : 1 < A := by nlinarith
  have hnorm : ∀ g, ‖v g‖ ^ 2 = (fullPhysicalEnergy (H g) q).toReal := by
    intro g
    exact historyTimeVector_norm_sq _ _ _ _ _ _ _
  have hordered : ∀ g h : Fin n, g < h →
      ‖inner ℂ (v g) (v h)‖ ^ 2 ≤ (A - 1)⁻¹ * ‖v g‖ ^ 2 * ‖v h‖ ^ 2 := by
    intro g h hgh
    have hb : 0 ≤ upper g := (hlo g).le.trans (hlohi g)
    have hba : upper g < lower h := by
      have hbpos : 0 < upper g := (hlo g).trans_le (hlohi g)
      nlinarith [hsep g h hgh]
    have he := separated_history_correlation_sq
      (I g) (z g) (σ g) (target g) (center g) (I h) (z h) (σ h) (target h) (center h)
      (hages g) (hages h) hb hba hA1 (hsep g h hgh) (hsthi g) (hstlo h)
    have hp : inner ℂ (v g) (v h) = historyPairing (H g) (H h) q :=
      toLp_inner_eq_integral (historyF_memLp_time _ _ _ _ _ (hages g) q)
        (historyF_memLp_time _ _ _ _ _ (hages h) q)
    rw [hp, hnorm, hnorm]
    exact he
  have hcross : ∀ g h : Fin n, g ≠ h →
      ‖inner ℂ (v g) (v h)‖ ^ 2 ≤ (A - 1)⁻¹ * ‖v g‖ ^ 2 * ‖v h‖ ^ 2 := by
    intro g h hgh
    rcases lt_or_gt_of_ne hgh with hlt | hgt
    · exact hordered g h hlt
    · rw [norm_inner_symm]
      have he := hordered h g hgt
      calc
        _ ≤ (A - 1)⁻¹ * ‖v h‖ ^ 2 * ‖v g‖ ^ 2 := he
        _ = _ := by ring
  have hframe := finite_frame_of_correlation hn v hA hcross
  have hm : ∀ g, MemLp (H g) 2 (volume.restrict (Ici q)) := by
    intro g
    exact historyF_memLp_time _ _ _ _ _ (hages g) q
  have hsum := memLp_finsetSum Finset.univ (fun g _ => hm g)
  rw [memLp_fullEnergy_norm_sq hsum, toLp_finsetSum Finset.univ H hm]
  change (1 / 2 : ℝ) * ∑ g, (fullPhysicalEnergy (H g) q).toReal ≤ ‖∑ g, v g‖ ^ 2
  simpa only [hnorm] using hframe

/-- A quadratic Gram bound produces a bounded map on the actual history range.
The extension is zero on its orthogonal complement, so singular covariances are allowed. -/
theorem range_factorization_of_bound {D H E : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : D →ₗ[ℂ] H) (B : D →ₗ[ℂ] E) [CompleteSpace A.range]
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x, ‖B x‖ ≤ K * ‖A x‖) :
    ∃ T : H →L[ℂ] E, ‖T‖ ≤ K ∧ (∀ x, T (A x) = B x) ∧
      T = T.comp A.range.starProjection := by
  have hker : A.ker ≤ B.ker := by
    intro x hx
    change B x = 0
    have hx' : A x = 0 := hx
    apply norm_eq_zero.mp
    have hh := hbound x
    rw [hx', norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  let L : A.range →ₗ[ℂ] E :=
    (A.ker.liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hL : ∀ x, L ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    intro x
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hb : ∀ y : A.range, ‖L y‖ ≤ K * ‖y‖ := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    have hy : y = ⟨A x, LinearMap.mem_range_self A x⟩ := Subtype.ext hx.symm
    rw [hy, hL]
    exact hbound x
  let S : A.range →L[ℂ] E := L.mkContinuous K hb
  let T : H →L[ℂ] E := S.comp A.range.orthogonalProjectionOnto
  refine ⟨T, ?_, ?_, ?_⟩
  · calc
      ‖T‖ ≤ ‖S‖ * ‖A.range.orthogonalProjectionOnto‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * 1 := mul_le_mul (LinearMap.mkContinuous_norm_le L hK hb)
        A.range.orthogonalProjectionOnto_norm_le
        (norm_nonneg A.range.orthogonalProjectionOnto) hK
      _ = K := mul_one _
  · intro x
    change S (A.range.orthogonalProjectionOnto (A x)) = B x
    have hp : A.range.orthogonalProjectionOnto (A x) = ⟨A x, LinearMap.mem_range_self A x⟩ :=
      A.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A x, LinearMap.mem_range_self A x⟩
    rw [hp]
    exact hL x
  · ext y
    change S (A.range.orthogonalProjectionOnto y) =
      S (A.range.orthogonalProjectionOnto (A.range.starProjection y))
    simp only [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem historyF_add_coeff {ι : Type*} (I : Finset ι) (z w : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) :
    historyF I (z + w) σ target center =
      historyF I z σ target center + historyF I w σ target center := by
  funext u
  simp only [historyF, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp only [add_smul, add_zero]

theorem historyF_smul_coeff {ι : Type*} (I : Finset ι) (z : ι → ℂ) (c : ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) :
    historyF I (c • z) σ target center = c • historyF I z σ target center := by
  funext u
  simp only [historyF, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp only [smul_smul, smul_zero, smul_eq_mul]

/-- The genuine linear observation-to-history map, realized in time/spatial L². -/
def historyLinearMap {ι : Type*} (I : Finset ι) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i) (q : ℝ) :
    (ι → ℂ) →ₗ[ℂ] Lp CircleL2 2 (volume.restrict (Ici q)) where
  toFun z := historyTimeVector I z σ target center hages q
  map_add' z w := by
    unfold historyTimeVector
    have he := historyF_add_coeff I z w σ target center
    exact (MemLp.toLp_congr _
      ((historyF_memLp_time I z σ target center hages q).add
        (historyF_memLp_time I w σ target center hages q))
      (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_add _ _)
  map_smul' c z := by
    unfold historyTimeVector
    have he := historyF_smul_coeff I z c σ target center
    exact (MemLp.toLp_congr _
      ((historyF_memLp_time I z σ target center hages q).const_smul c)
      (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_const_smul _ _)

/-- The current undamped observation row as a linear map of its coefficients. -/
def currentLinearMap {ι : Type*} (I : Finset ι) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (q : ℝ) : (ι → ℂ) →ₗ[ℂ] CircleL2 where
  toFun z := historyF I z σ target center q
  map_add' z w := congrFun (historyF_add_coeff I z w σ target center) q
  map_smul' c z := congrFun (historyF_smul_coeff I z c σ target center) q

/-- Actual current-row factorization through the original history span, including collisions. -/
theorem current_history_range_factorization {ι : Type*} [Fintype ι]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {q δ : ℝ} (hδ : 0 < δ)
    (hstop : ∀ i ∈ I, q + δ ≤ σ i) :
    ∃ T : Lp CircleL2 2 (volume.restrict (Ici q)) →L[ℂ] CircleL2,
      ‖T‖ ≤ Real.sqrt (2 / δ) ∧
      (∀ z, T (historyTimeVector I z σ target center hages q) =
        historyF I z σ target center q) ∧
      T = T.comp (historyLinearMap I σ target center hages q).range.starProjection := by
  apply range_factorization_of_bound (historyLinearMap I σ target center hages q)
    (currentLinearMap I σ target center q) (Real.sqrt_nonneg _)
  intro z
  have he := stopped_current_row_bound I z σ target center hages hδ hstop
  rw [← historyTimeVector_norm_sq I z σ target center hages q] at he
  have hc : 0 ≤ 2 / δ := by positivity
  have hs := Real.sq_sqrt hc
  change ‖historyF I z σ target center q‖ ≤
    Real.sqrt (2 / δ) * ‖historyTimeVector I z σ target center hages q‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rwa [mul_pow, hs]

theorem historyG_add_coeff {ι : Type*} (I : Finset ι) (z w : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (Λ : ℝ) :
    historyG I (z + w) σ target center Λ =
      historyG I z σ target center Λ + historyG I w σ target center Λ := by
  funext u
  simp only [historyG, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp only [add_smul, smul_add, add_zero]

theorem historyG_smul_coeff {ι : Type*} (I : Finset ι) (z : ι → ℂ) (c : ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (Λ : ℝ) :
    historyG I (c • z) σ target center Λ = c • historyG I z σ target center Λ := by
  funext u
  simp only [historyG, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · simp only [smul_smul, smul_eq_mul]
    congr 1
    ring
  · simp only [smul_zero]

def dampedCurrentLinearMap {ι : Type*} (I : Finset ι) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (Λ q : ℝ) : (ι → ℂ) →ₗ[ℂ] CircleL2 where
  toFun z := historyG I z σ target center Λ q
  map_add' z w := congrFun (historyG_add_coeff I z w σ target center Λ) q
  map_smul' c z := congrFun (historyG_smul_coeff I z c σ target center Λ) q

/-- The damped current row factors through the original, undamped history span. -/
theorem damped_current_history_range_factorization {ι : Type*} [Fintype ι]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {Λ q δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ)
    (hstop : ∀ i ∈ I, q + δ ≤ σ i) :
    ∃ T : Lp CircleL2 2 (volume.restrict (Ici q)) →L[ℂ] CircleL2,
      ‖T‖ ≤ Real.sqrt (2 / δ) ∧
      (∀ z, T (historyTimeVector I z σ target center hages q) =
        historyG I z σ target center Λ q) ∧
      T = T.comp (historyLinearMap I σ target center hages q).range.starProjection := by
  apply range_factorization_of_bound (historyLinearMap I σ target center hages q)
    (dampedCurrentLinearMap I σ target center Λ q) (Real.sqrt_nonneg _)
  intro z
  have he := stopped_damped_current_row_bound I z σ target center hages hΛ hδ hstop
  rw [← historyTimeVector_norm_sq I z σ target center hages q] at he
  have hs := Real.sq_sqrt (show 0 ≤ 2 / δ by positivity)
  change ‖historyG I z σ target center Λ q‖ ≤
    Real.sqrt (2 / δ) * ‖historyTimeVector I z σ target center hages q‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rwa [mul_pow, hs]

/-- The clipped defect row factors through the actual original history range.
Its operator norm retains the factor `min 1 (Λ*w)` before any absolute kernel estimate. -/
theorem defect_current_history_range_factorization {ι : Type*} [Fintype ι]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {Λ q w M : ℝ}
    (hΛ : 0 < Λ) (hw : 0 < w) (hM : 1 ≤ M)
    (hlower : ∀ i ∈ I, q + w ≤ σ i) (hupper : ∀ i ∈ I, σ i ≤ q + M * w) :
    ∃ T : Lp CircleL2 2 (volume.restrict (Ici q)) →L[ℂ] CircleL2,
      ‖T‖ ≤ Real.sqrt (max M 8 / w) * min 1 (Λ * w) ∧
      (∀ z, T (historyTimeVector I z σ target center hages q) =
        historyF I z σ target center q - historyG I z σ target center Λ q) ∧
      T = T.comp (historyLinearMap I σ target center hages q).range.starProjection := by
  have hr : 0 ≤ min 1 (Λ * w) := le_min (by norm_num) (mul_nonneg hΛ.le hw.le)
  have hc : 0 ≤ max M 8 / w := by positivity
  apply range_factorization_of_bound (historyLinearMap I σ target center hages q)
    (currentLinearMap I σ target center q - dampedCurrentLinearMap I σ target center Λ q)
    (mul_nonneg (Real.sqrt_nonneg _) hr)
  intro z
  have he := stopped_current_difference_clipped I z σ target center hages hΛ hw hM hlower hupper
  rw [← historyTimeVector_norm_sq I z σ target center hages q] at he
  change ‖historyF I z σ target center q - historyG I z σ target center Λ q‖ ≤
    (Real.sqrt (max M 8 / w) * min 1 (Λ * w)) *
      ‖historyTimeVector I z σ target center hages q‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hc]
  convert he using 1
  ring

/-- A single group can reserve half of the actual full-history covariance. -/
theorem separated_group_energy_le {ι : Type*} {n : ℕ} (hn : 0 < n)
    (I : Fin n → Finset ι) (z : Fin n → ι → ℂ) (σ target : Fin n → ι → ℝ)
    (center : Fin n → ι → HeatCircle) (hages : ∀ g, ∀ i ∈ I g, σ g i ≤ target g i)
    (lower upper : Fin n → ℝ) {q A : ℝ} (hA : 4 * (n : ℝ) ^ 2 + 1 ≤ A)
    (hlo : ∀ g, 0 < lower g) (hlohi : ∀ g, lower g ≤ upper g)
    (hstlo : ∀ g, ∀ i ∈ I g, q + lower g ≤ σ g i)
    (hsthi : ∀ g, ∀ i ∈ I g, σ g i ≤ q + upper g)
    (hsep : ∀ g h, g < h → A * upper g ≤ lower h) (g : Fin n) :
    (fullPhysicalEnergy (historyF (I g) (z g) (σ g) (target g) (center g)) q).toReal ≤
      2 * (fullPhysicalEnergy (fun u => ∑ h : Fin n,
        historyF (I h) (z h) (σ h) (target h) (center h) u) q).toReal := by
  have hf := separated_history_covariance_frame hn I z σ target center hages lower upper
    hA hlo hlohi hstlo hsthi hsep
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun h => (fullPhysicalEnergy (historyF (I h) (z h) (σ h) (target h) (center h)) q).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ g)
  linarith

/-- Sum of the original physical histories, as a linear map of all original coefficients. -/
def groupedHistoryLinearMap {ι : Type*} {n : ℕ}
    (I : Fin n → Finset ι) (σ target : Fin n → ι → ℝ)
    (center : Fin n → ι → HeatCircle) (hages : ∀ g, ∀ i ∈ I g, σ g i ≤ target g i)
    (q : ℝ) : (Fin n → ι → ℂ) →ₗ[ℂ] Lp CircleL2 2 (volume.restrict (Ici q)) :=
  ∑ g : Fin n, (historyLinearMap (I g) (σ g) (target g) (center g) (hages g) q).comp
    (LinearMap.proj g)

theorem groupedHistoryLinearMap_norm_sq {ι : Type*} {n : ℕ}
    (I : Fin n → Finset ι) (σ target : Fin n → ι → ℝ)
    (center : Fin n → ι → HeatCircle) (hages : ∀ g, ∀ i ∈ I g, σ g i ≤ target g i)
    (q : ℝ) (z : Fin n → ι → ℂ) :
    ‖groupedHistoryLinearMap I σ target center hages q z‖ ^ 2 =
      (fullPhysicalEnergy (fun u => ∑ g : Fin n,
        historyF (I g) (z g) (σ g) (target g) (center g) u) q).toReal := by
  have hm : ∀ g, MemLp (historyF (I g) (z g) (σ g) (target g) (center g)) 2
      (volume.restrict (Ici q)) := fun g => historyF_memLp_time _ _ _ _ _ (hages g) q
  rw [memLp_fullEnergy_norm_sq (memLp_finsetSum Finset.univ (fun g _ => hm g)),
    toLp_finsetSum Finset.univ _ hm]
  simp only [groupedHistoryLinearMap, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

/-- The all-age clipped current row of any group factors through the full physical
history covariance. The assumptions contain age geometry only. -/
theorem separated_group_defect_range_factorization {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 0 < n) (I : Fin n → Finset ι) (σ target : Fin n → ι → ℝ)
    (center : Fin n → ι → HeatCircle) (hages : ∀ g, ∀ i ∈ I g, σ g i ≤ target g i)
    (lower upper : Fin n → ℝ) {Λ q A M : ℝ} (hΛ : 0 < Λ)
    (hA : 4 * (n : ℝ) ^ 2 + 1 ≤ A) (hM : 1 ≤ M)
    (hlo : ∀ g, 0 < lower g) (hlohi : ∀ g, lower g ≤ upper g)
    (hcompare : ∀ g, upper g ≤ M * lower g)
    (hstlo : ∀ g, ∀ i ∈ I g, q + lower g ≤ σ g i)
    (hsthi : ∀ g, ∀ i ∈ I g, σ g i ≤ q + upper g)
    (hsep : ∀ g h, g < h → A * upper g ≤ lower h) (g : Fin n) :
    ∃ T : Lp CircleL2 2 (volume.restrict (Ici q)) →L[ℂ] CircleL2,
      ‖T‖ ≤ Real.sqrt (2 * max M 8 / lower g) * min 1 (Λ * lower g) ∧
      (∀ z, T (groupedHistoryLinearMap I σ target center hages q z) =
        historyF (I g) (z g) (σ g) (target g) (center g) q -
          historyG (I g) (z g) (σ g) (target g) (center g) Λ q) ∧
      T = T.comp (groupedHistoryLinearMap I σ target center hages q).range.starProjection := by
  have hr : 0 ≤ min 1 (Λ * lower g) := le_min (by norm_num) (mul_nonneg hΛ.le (hlo g).le)
  have hmax : 0 ≤ max M 8 := by linarith [le_max_right M 8]
  have hc : 0 ≤ 2 * max M 8 / lower g := by exact div_nonneg (by positivity) (hlo g).le
  apply range_factorization_of_bound (groupedHistoryLinearMap I σ target center hages q)
    ((currentLinearMap (I g) (σ g) (target g) (center g) q -
      dampedCurrentLinearMap (I g) (σ g) (target g) (center g) Λ q).comp (LinearMap.proj g))
    (mul_nonneg (Real.sqrt_nonneg _) hr)
  intro z
  have he := stopped_current_difference_clipped (I g) (z g) (σ g) (target g) (center g)
    (hages g) hΛ (hlo g) hM (hstlo g) (fun i hi => (hsthi g i hi).trans (by linarith [hcompare g]))
  have hf := separated_group_energy_le hn I z σ target center hages lower upper
    hA hlo hlohi hstlo hsthi hsep g
  have hk : 0 ≤ max M 8 * min 1 (Λ * lower g) ^ 2 * (lower g)⁻¹ :=
    mul_nonneg (mul_nonneg hmax (sq_nonneg _)) (inv_nonneg.mpr (hlo g).le)
  have hb := he.trans (mul_le_mul_of_nonneg_left hf hk)
  rw [← groupedHistoryLinearMap_norm_sq I σ target center hages q z] at hb
  change ‖historyF (I g) (z g) (σ g) (target g) (center g) q -
      historyG (I g) (z g) (σ g) (target g) (center g) Λ q‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hc]
  convert hb using 1
  ring

/-- A bounded diagonal multiplier on the complete circle Fourier representation. -/
def fourierDiagonalLinearMap (m : ℤ → ℂ) (hm : ∀ n, ‖m n‖ ≤ 1) :
    lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun f := ⟨fun n => m n * f n, (lp.memℓp f).norm.mono (fun n => by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f n)))⟩
  map_add' f g := by
    apply lp.ext
    funext n
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply lp.ext
    funext n
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem fourierDiagonalLinearMap_norm_le (m : ℤ → ℂ) (hm : ∀ n, ‖m n‖ ≤ 1)
    (f : lp (fun _ : ℤ => ℂ) 2) : ‖fourierDiagonalLinearMap m hm f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  change ‖m n * f n‖ ≤ ‖f n‖
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f n))

def fourierDiagonal (m : ℤ → ℂ) (hm : ∀ n, ‖m n‖ ≤ 1) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  (fourierDiagonalLinearMap m hm).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using fourierDiagonalLinearMap_norm_le m hm f)

theorem heatMultiplier_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℤ) :
    ‖(Real.exp (-t * (n : ℝ) ^ 2) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))

/-- The actual contractive heat semigroup on the circle L² space. -/
def circleHeatOperator (t : ℝ) (ht : 0 ≤ t) : CircleL2 →L[ℂ] CircleL2 :=
  (fourierBasis (T := 2 * Real.pi)).repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((fourierDiagonal (fun n => (Real.exp (-t * (n : ℝ) ^ 2) : ℂ))
      (heatMultiplier_le_one ht)).comp
        (fourierBasis (T := 2 * Real.pi)).repr.toLinearIsometry.toContinuousLinearMap)

theorem circleHeatOperator_fourierCoeff (t : ℝ) (ht : 0 ≤ t) (f : CircleL2) (n : ℤ) :
    fourierCoeff (circleHeatOperator t ht f) n =
      (Real.exp (-t * (n : ℝ) ^ 2) : ℂ) * fourierCoeff f n := by
  rw [← fourierBasis_repr]
  change ((fourierBasis (T := 2 * Real.pi)).repr
    ((fourierBasis (T := 2 * Real.pi)).repr.symm _)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (Real.exp (-t * (n : ℝ) ^ 2) : ℂ) *
    (fourierBasis (T := 2 * Real.pi)).repr f n = _
  rw [fourierBasis_repr]

theorem circleHeatOperator_norm_le (t : ℝ) (ht : 0 ≤ t) (f : CircleL2) :
    ‖circleHeatOperator t ht f‖ ≤ ‖f‖ := by
  change ‖(fourierBasis (T := 2 * Real.pi)).repr.symm
    ((fourierDiagonal (fun n => (Real.exp (-t * (n : ℝ) ^ 2) : ℂ))
      (heatMultiplier_le_one ht)) ((fourierBasis (T := 2 * Real.pi)).repr f))‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact (fourierDiagonalLinearMap_norm_le _ (heatMultiplier_le_one ht) _).trans_eq
    (LinearIsometryEquiv.norm_map _ _)

theorem circleHeatOperator_heat {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (x : HeatCircle) :
    circleHeatOperator t ht (circleHeat a x) = circleHeat (t + a) x := by
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr, circleHeatOperator_fourierCoeff,
    circleHeat_fourierCoeff ha, circleHeat_fourierCoeff (show 0 < t + a by linarith), heatCoeff]
  rw [mul_left_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -t * (n : ℝ) ^ 2 + -a * (n : ℝ) ^ 2 = -(t + a) * (n : ℝ) ^ 2 by ring]

/-- Exact semigroup propagation before the first stop, retaining the original targets. -/
theorem historyG_heat_propagation {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    (Λ : ℝ) {q u : ℝ} (hqu : q ≤ u) (hactive : ∀ i ∈ I, u < σ i) :
    historyG I z σ target center Λ q = (Real.exp (-Λ * (u - q)) : ℂ) •
      circleHeatOperator (u - q) (sub_nonneg.mpr hqu) (historyG I z σ target center Λ u) := by
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  apply lp.ext
  funext n
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, fourierBasis_repr,
    circleHeatOperator_fourierCoeff, smul_eq_mul]
  rw [historyG_fourierCoeff I z σ target center hages,
    historyG_fourierCoeff I z σ target center hages]
  have heq : (∑ i ∈ I, (Real.exp (-Λ * (σ i - q)) *
      stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) q) • (z i * fourier (-n) (center i))) =
      Real.exp (-(u - q) * (Λ + (n : ℝ) ^ 2)) •
      (∑ i ∈ I, (Real.exp (-Λ * (σ i - u)) *
        stoppedModeF ((n : ℝ) ^ 2) (σ i) (target i) u) • (z i * fourier (-n) (center i))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [damped_mode_propagation hqu (hactive i hi), mul_smul]
  rw [heq, show -(u - q) * (Λ + (n : ℝ) ^ 2) =
    -Λ * (u - q) + -(u - q) * (n : ℝ) ^ 2 by ring, Real.exp_add]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem fullPhysicalEnergy_mono {H : ℝ → CircleL2} {q r : ℝ} (hqr : q ≤ r) :
    fullPhysicalEnergy H r ≤ fullPhysicalEnergy H q := by
  apply lintegral_mono_set
  exact Ici_subset_Ici.mpr hqr

/-- A damped current row keeps a genuine positive heat factor after reserving half
of the future stopping age. The middle map is controlled by the original full history. -/
theorem damped_current_history_heat_factorization {ι : Type*} [Fintype ι]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {Λ q δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ)
    (hstop : ∀ i ∈ I, q + δ ≤ σ i) :
    ∃ T : Lp CircleL2 2 (volume.restrict (Ici q)) →L[ℂ] CircleL2,
      ‖T‖ ≤ Real.sqrt (4 / δ) ∧
      (∀ z, historyG I z σ target center Λ q = (Real.exp (-Λ * (δ / 2)) : ℂ) •
        circleHeatOperator (δ / 2) (by positivity)
          (T (historyTimeVector I z σ target center hages q))) ∧
      T = T.comp (historyLinearMap I σ target center hages q).range.starProjection := by
  have hbound : ∀ z, ‖historyG I z σ target center Λ (q + δ / 2)‖ ≤
      Real.sqrt (4 / δ) * ‖historyTimeVector I z σ target center hages q‖ := by
    intro z
    have hb := stopped_damped_current_row_bound I z σ target center hages hΛ
      (show 0 < δ / 2 by positivity) (q := q + δ / 2) (fun i hi => by linarith [hstop i hi])
    have hfin := (full_stopped_history_contraction I z σ target center
      (q := q) hΛ hages).2.1
    have he := ENNReal.toReal_mono hfin.ne (fullPhysicalEnergy_mono
      (H := historyF I z σ target center) (show q ≤ q + δ / 2 by linarith))
    have hs := hb.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 / (δ / 2)))
    rw [← historyTimeVector_norm_sq I z σ target center hages q] at hs
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ 4 / δ by positivity)]
    convert hs using 1
    field_simp
    ring
  obtain ⟨T, hT, happly, hproj⟩ := range_factorization_of_bound
    (historyLinearMap I σ target center hages q)
    (dampedCurrentLinearMap I σ target center Λ (q + δ / 2)) (Real.sqrt_nonneg _) hbound
  refine ⟨T, hT, ?_, hproj⟩
  intro z
  have htz : T (historyTimeVector I z σ target center hages q) =
      historyG I z σ target center Λ (q + δ / 2) := happly z
  rw [htz]
  have hp := historyG_heat_propagation I z σ target center hages Λ
    (show q ≤ q + δ / 2 by linarith) (fun i hi => by linarith [hstop i hi])
  simpa only [show q + δ / 2 - q = δ / 2 by ring] using hp

theorem circleHeatOperator_self_adjoint (t : ℝ) (ht : 0 ≤ t) (f g : CircleL2) :
    inner ℂ (circleHeatOperator t ht f) g = inner ℂ f (circleHeatOperator t ht g) := by
  rw [← (fourierBasis (T := 2 * Real.pi)).repr.inner_map_map,
    ← (fourierBasis (T := 2 * Real.pi)).repr.inner_map_map, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [fourierBasis_repr, circleHeatOperator_fourierCoeff]
  change inner ℂ ((Real.exp (-t * (n : ℝ) ^ 2) : ℂ) • fourierCoeff f n) (fourierCoeff g n) =
    inner ℂ (fourierCoeff f n) ((Real.exp (-t * (n : ℝ) ^ 2) : ℂ) • fourierCoeff g n)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- The damped first row, paired against an arbitrary signed input, retains a genuine
right heat factor and the original covariance energy. -/
theorem damped_current_mean_input_bound {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    (σ target : ι → ℝ) (center : ι → HeatCircle) (hages : ∀ i ∈ I, σ i ≤ target i)
    {Λ q δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (hstop : ∀ i ∈ I, q + δ ≤ σ i)
    (d : CircleL2) :
    ‖inner ℂ (historyG I z σ target center Λ q) d‖ ^ 2 ≤
      (4 / δ) * ‖circleHeatOperator (δ / 2) (by positivity) d‖ ^ 2 *
        (fullPhysicalEnergy (historyF I z σ target center) q).toReal := by
  have hp := historyG_heat_propagation I z σ target center hages Λ
    (show q ≤ q + δ / 2 by linarith) (fun i hi => by linarith [hstop i hi])
  have hb := stopped_damped_current_row_bound I z σ target center hages hΛ
    (show 0 < δ / 2 by positivity) (q := q + δ / 2) (fun i hi => by linarith [hstop i hi])
  have hfin := (full_stopped_history_contraction I z σ target center (q := q) hΛ hages).2.1
  have he := ENNReal.toReal_mono hfin.ne (fullPhysicalEnergy_mono
    (H := historyF I z σ target center) (show q ≤ q + δ / 2 by linarith))
  have hs := hb.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 / (δ / 2)))
  have hscalar : ‖(Real.exp (-Λ * (δ / 2)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  simp only [show q + δ / 2 - q = δ / 2 by ring] at hp
  rw [hp, inner_smul_left, norm_mul, Complex.norm_conj,
    circleHeatOperator_self_adjoint]
  have hc := norm_inner_le_norm (𝕜 := ℂ) (historyG I z σ target center Λ (q + δ / 2))
    (circleHeatOperator (δ / 2) (show 0 ≤ δ / 2 by positivity) d)
  have hn := mul_le_mul_of_nonneg_left hc (norm_nonneg (Real.exp (-Λ * (δ / 2)) : ℂ))
  have hn' : ‖(Real.exp (-Λ * (δ / 2)) : ℂ)‖ *
      ‖inner ℂ (historyG I z σ target center Λ (q + δ / 2))
        (circleHeatOperator (δ / 2) (by positivity) d)‖ ≤
      ‖historyG I z σ target center Λ (q + δ / 2)‖ *
        ‖circleHeatOperator (δ / 2) (by positivity) d‖ :=
    hn.trans (mul_le_of_le_one_left (by positivity) hscalar)
  calc
    _ ≤ (‖historyG I z σ target center Λ (q + δ / 2)‖ *
        ‖circleHeatOperator (δ / 2) (by positivity) d‖) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hn'
    _ ≤ _ := by
      rw [mul_pow]
      have hh := mul_le_mul_of_nonneg_right hs
        (sq_nonneg ‖circleHeatOperator (δ / 2) (show 0 ≤ δ / 2 by positivity) d‖)
      convert hh using 1
      field_simp
      ring

set_option maxHeartbeats 1000000 in
/-- A lower Gaussian heat trace, obtained by integrating the monotone frequency profile. -/
theorem circleHeat_norm_sq_lower {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    HeatTrace.fractionalGaussianIntegral 0 * (2 * t) ^ (-(1 / 2 : ℝ)) ≤
      ‖circleHeat t x‖ ^ 2 := by
  have hnat := HeatTrace.multiplier_nat_summable (Λ := 1) (ρ := 0) (t := 2 * t)
    (by norm_num) le_rfl (by linarith)
  have hint := (HeatTrace.multiplier_antitone (Λ := 1) (ρ := 0) (t := 2 * t)
    (by norm_num) le_rfl (by linarith)).integral_le_tsum hnat
    (fun _ _ => HeatTrace.multiplier_nonneg (by norm_num : (0 : ℝ) ≤ 1))
  have hi := HeatTrace.fractional_gaussian_integral (ρ := 0) (by norm_num : (0 : ℝ) < 1 / 2)
    (show 0 < 2 * t by linarith)
  simp only [HeatTrace.multiplier, neg_zero, Real.rpow_zero, one_mul] at hint
  simp only [mul_zero, Real.rpow_zero, one_mul, zero_sub] at hi
  rw [hi] at hint
  have hs := hasSum_sq_fourierCoeff (circleHeat t x)
  rw [circle_spatial_energy_eq_norm_sq] at hs
  simp_rw [circleHeat_fourierCoeff ht, heatCoeff_norm_sq] at hs
  have hn : Summable (fun n : ℕ => Real.exp (-(2 * t) * (n : ℝ) ^ 2)) := by
    simpa only [HeatTrace.multiplier, neg_zero, Real.rpow_zero, one_mul] using hnat
  have hcmp := Summable.tsum_le_tsum_of_inj (fun n : ℕ => (n : ℤ)) Int.ofNat_injective
    (fun _ _ => (Real.exp_pos _).le) (fun _ => le_rfl) hn hs.summable
  exact hint.trans (hcmp.trans_eq hs.tsum_eq)

/-- The normalized Fourier envelope for a single actual heat generator. -/
theorem single_heat_fourier_envelope {t : ℝ} (ht : 0 < t) (x : HeatCircle) (n : ℤ) :
    ‖fourierCoeff (circleHeat t x) n‖ ^ 2 ≤
      ((2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0) *
        Real.exp (-(2 * t) * (n : ℝ) ^ 2) * ‖circleHeat t x‖ ^ 2 := by
  have hl := circleHeat_norm_sq_lower ht x
  have hG : 0 < HeatTrace.fractionalGaussianIntegral 0 :=
    HeatTrace.fractionalGaussianIntegral_pos (by norm_num)
  have hp : 0 < (2 * t) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hr : (2 * t) ^ (-(1 / 2 : ℝ)) = ((2 * t) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg (by linarith) _
  rw [hr] at hl
  have he : 1 ≤ ((2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0) *
      ‖circleHeat t x‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hG).mpr
    rw [one_mul]
    have hh := (div_le_iff₀ hp).mp (show HeatTrace.fractionalGaussianIntegral 0 /
      (2 * t) ^ (1 / 2 : ℝ) ≤ ‖circleHeat t x‖ ^ 2 by exact hl)
    nlinarith
  rw [circleHeat_fourierCoeff ht, heatCoeff_norm_sq]
  have hh := mul_le_mul_of_nonneg_left he (Real.exp_pos (-(2 * t) * (n : ℝ) ^ 2)).le
  nlinarith

theorem single_heat_span_fourier_envelope {t : ℝ} (ht : 0 < t) (x : HeatCircle)
    {f : CircleL2} (hf : f ∈ Submodule.span ℂ {circleHeat t x}) (n : ℤ) :
    ‖fourierCoeff f n‖ ^ 2 ≤
      ((2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0) *
        Real.exp (-(2 * t) * (n : ℝ) ^ 2) * ‖f‖ ^ 2 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have hb := mul_le_mul_of_nonneg_left (single_heat_fourier_envelope ht x n) (sq_nonneg ‖c‖)
  simp only [← fourierBasis_repr, map_smul, lp.coeFn_smul, Pi.smul_apply, norm_smul, mul_pow]
  simp only [fourierBasis_repr]
  convert hb using 1
  ring

/-- Pointwise heat-kernel duality in the complete Fourier basis. -/
theorem heat_kernel_inner_hasSum {t : ℝ} (ht : 0 < t) (x : HeatCircle) (d : CircleL2) :
    HasSum (fun n : ℤ => (Real.exp (-t * (n : ℝ) ^ 2) : ℂ) * fourierCoeff d n * fourier n x)
      (inner ℂ (circleHeat t x) d) := by
  have hs := (fourierBasis (T := 2 * Real.pi)).hasSum_inner_mul_inner (circleHeat t x) d
  convert hs using 1
  funext n
  rw [← inner_conj_symm (circleHeat t x) (fourierBasis n),
    ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
    fourierBasis_repr, fourierBasis_repr, circleHeat_fourierCoeff ht]
  simp only [heatCoeff, map_mul, fourier_neg, starRingEnd_self_apply, Complex.conj_ofReal]
  ring

theorem heat_fourier_series_norm_summable {t : ℝ} (ht : 0 < t) (d : CircleL2) :
    Summable (fun n : ℤ => ‖(Real.exp (-t * (n : ℝ) ^ 2) : ℂ) * fourierCoeff d n‖) := by
  let h : lp (fun _ : ℤ => ℂ) 2 := ⟨heatCoeff t 0, heatCoeff_memℓp ht 0⟩
  have hs := lp.summable_mul (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
    h ((fourierBasis (T := 2 * Real.pi)).repr d)
  simpa only [h, heatCoeff, fourier_eval_zero, one_mul, fourierBasis_repr, norm_mul] using hs

/-- The physical heat-kernel pairing is exactly the actual smoothed input almost everywhere. -/
theorem heat_kernel_inner_ae {t : ℝ} (ht : 0 < t) (d : CircleL2) :
    (fun x : HeatCircle => inner ℂ (circleHeat t x) d) =ᵐ[haarAddCircle]
      (circleHeatOperator t ht.le d : HeatCircle → ℂ) := by
  let b := fourierBasis (T := 2 * Real.pi)
  let f : ℤ → CircleL2 := fun n =>
    fourierCoeff (circleHeatOperator t ht.le d) n • b n
  have hsum : HasSum f (circleHeatOperator t ht.le d) := by
    simpa only [f, b, fourierBasis_repr] using b.hasSum_repr (circleHeatOperator t ht.le d)
  have hn : Summable (fun n => ‖f n‖) := by
    simpa only [f, norm_smul, b.orthonormal.norm_eq_one, mul_one,
      circleHeatOperator_fourierCoeff] using heat_fourier_series_norm_summable ht d
  have hae := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn)
  have hterms : ∀ᵐ x : HeatCircle ∂haarAddCircle, ∀ n : ℤ,
      f n x = (Real.exp (-t * (n : ℝ) ^ 2) : ℂ) * fourierCoeff d n * fourier n x := by
    apply ae_all_iff.mpr
    intro n
    have hsmul := Lp.coeFn_smul (fourierCoeff (circleHeatOperator t ht.le d) n) (b n)
    have hb : (b n : HeatCircle → ℂ) =ᵐ[haarAddCircle] fourier n := by
      simpa only [b, coe_fourierBasis] using coeFn_fourierLp 2 n
    filter_upwards [hsmul, hb] with x hx hbx
    change (fourierCoeff (circleHeatOperator t ht.le d) n • b n : CircleL2) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hbx, circleHeatOperator_fourierCoeff]
  rw [hsum.tsum_eq] at hae
  filter_upwards [hae, hterms] with x hx htx
  have hp := heat_kernel_inner_hasSum ht x d
  have hx' := hx.congr_fun (fun n => (htx n).symm)
  exact hp.unique hx'

/-- Exact signed one-input integration for one translated physical heat row. -/
theorem heat_kernel_inner_energy {t : ℝ} (ht : 0 < t) (d : CircleL2) :
    (∫ x : HeatCircle, ‖inner ℂ (circleHeat t x) d‖ ^ 2 ∂haarAddCircle) =
      ‖circleHeatOperator t ht.le d‖ ^ 2 := by
  rw [L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [heat_kernel_inner_ae ht d] with x hx
  rw [hx]

/-- Translation-integrated projection bound for the actual one-generator heat span. -/
theorem single_heat_span_input_energy {t : ℝ} (ht : 0 < t) (d : CircleL2) :
    (∫ x : HeatCircle, ‖inner ℂ (circleHeat t x) d‖ ^ 2 / ‖circleHeat t x‖ ^ 2 ∂haarAddCircle) ≤
      ((2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0) *
        ‖circleHeatOperator t ht.le d‖ ^ 2 := by
  let C : ℝ := (2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0
  have hG : 0 < HeatTrace.fractionalGaussianIntegral 0 :=
    HeatTrace.fractionalGaussianIntegral_pos (by norm_num)
  have hp : 0 < (2 * t) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hl : ∀ x : HeatCircle, 0 < ‖circleHeat t x‖ ^ 2 := by
    intro x
    exact (mul_pos hG (Real.rpow_pos_of_pos (by linarith) _)).trans_le (circleHeat_norm_sq_lower ht x)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint : ∀ x : HeatCircle, (‖circleHeat t x‖ ^ 2)⁻¹ ≤ C := by
    intro x
    apply (inv_le_iff_one_le_mul₀ (hl x)).mpr
    have hh := circleHeat_norm_sq_lower ht x
    rw [Real.rpow_neg (show 0 ≤ 2 * t by linarith)] at hh
    have hh' := (div_le_iff₀ hp).mp hh
    dsimp [C]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hG).mpr (by nlinarith)
  have he : Integrable (fun x : HeatCircle => ‖inner ℂ (circleHeat t x) d‖ ^ 2) haarAddCircle := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp (circleHeatOperator t ht.le d)).aestronglyMeasurable).mp
      (Lp.memLp (circleHeatOperator t ht.le d))
    exact hi.congr (by filter_upwards [heat_kernel_inner_ae ht d] with x hx; rw [hx])
  have hden : ∀ x : HeatCircle, ‖circleHeat t x‖ ^ 2 = ‖circleHeat t 0‖ ^ 2 := by
    intro x
    have hx := hasSum_sq_fourierCoeff (circleHeat t x)
    have h0 := hasSum_sq_fourierCoeff (circleHeat t 0)
    rw [circle_spatial_energy_eq_norm_sq] at hx h0
    simp_rw [circleHeat_fourierCoeff ht, heatCoeff_norm_sq] at hx h0
    exact hx.unique h0
  have hleft : Integrable (fun x : HeatCircle =>
      ‖inner ℂ (circleHeat t x) d‖ ^ 2 / ‖circleHeat t x‖ ^ 2) haarAddCircle := by
    simpa only [hden] using he.div_const (‖circleHeat t 0‖ ^ 2)
  calc
    _ ≤ ∫ x : HeatCircle, C * ‖inner ℂ (circleHeat t x) d‖ ^ 2 ∂haarAddCircle := by
      apply integral_mono hleft (he.const_mul C)
      intro x
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left (hpoint x) (sq_nonneg ‖inner ℂ (circleHeat t x) d‖)
    _ = C * ‖circleHeatOperator t ht.le d‖ ^ 2 := by rw [integral_const_mul, heat_kernel_inner_energy ht d]

theorem single_heat_projection_norm_sq (t : ℝ) (x : HeatCircle) (d : CircleL2) :
    ‖(Submodule.span ℂ {circleHeat t x}).starProjection d‖ ^ 2 =
      ‖inner ℂ (circleHeat t x) d‖ ^ 2 / ‖circleHeat t x‖ ^ 2 := by
  by_cases hh : circleHeat t x = 0
  · simp only [hh, Submodule.span_zero_singleton, Submodule.starProjection_bot,
      zero_apply, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), inner_zero_left,
      zero_div]
  · have hn : ‖circleHeat t x‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    rw [Submodule.starProjection_singleton ℂ d, norm_smul, norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (sq_nonneg _), mul_pow, div_pow]
    field_simp

theorem single_heat_projection_energy {t : ℝ} (ht : 0 < t) (d : CircleL2) :
    (∫ x : HeatCircle, ‖(Submodule.span ℂ {circleHeat t x}).starProjection d‖ ^ 2 ∂haarAddCircle) ≤
      ((2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0) *
        ‖circleHeatOperator t ht.le d‖ ^ 2 := by
  simp_rw [single_heat_projection_norm_sq]
  exact single_heat_span_input_energy ht d

theorem single_heat_projection_integrable {t : ℝ} (ht : 0 < t) (d : CircleL2) :
    Integrable (fun x : HeatCircle =>
      ‖(Submodule.span ℂ {circleHeat t x}).starProjection d‖ ^ 2) haarAddCircle := by
  have he : Integrable (fun x : HeatCircle => ‖inner ℂ (circleHeat t x) d‖ ^ 2) haarAddCircle := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp (circleHeatOperator t ht.le d)).aestronglyMeasurable).mp
      (Lp.memLp (circleHeatOperator t ht.le d))
    exact hi.congr (by filter_upwards [heat_kernel_inner_ae ht d] with x hx; rw [hx])
  have hden : ∀ x : HeatCircle, ‖circleHeat t x‖ ^ 2 = ‖circleHeat t 0‖ ^ 2 := by
    intro x
    have hx := hasSum_sq_fourierCoeff (circleHeat t x)
    have h0 := hasSum_sq_fourierCoeff (circleHeat t 0)
    rw [circle_spatial_energy_eq_norm_sq] at hx h0
    simp_rw [circleHeat_fourierCoeff ht, heatCoeff_norm_sq] at hx h0
    exact hx.unique h0
  simpa only [single_heat_projection_norm_sq, hden] using he.div_const (‖circleHeat t 0‖ ^ 2)

/-- Genuine one-generator translation-integrated Hilbert--Schmidt column estimate,
with the signed input smoothed before its norm is taken. -/
theorem single_heat_projection_hilbertSchmidt {ι : Type*} (I : Finset ι)
    {t : ℝ} (ht : 0 < t) (B : ι → CircleL2) :
    (∫ x : HeatCircle, (∑ j ∈ I,
      ‖(Submodule.span ℂ {circleHeat t x}).starProjection (B j)‖ ^ 2) ∂haarAddCircle) ≤
      ((2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0) *
        ∑ j ∈ I, ‖circleHeatOperator t ht.le (B j)‖ ^ 2 := by
  rw [integral_finsetSum I (fun j _ => single_heat_projection_integrable ht (B j)), Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => single_heat_projection_energy ht (B j))

/-- The countable-column Hilbert--Schmidt estimate uses positive Tonelli integration. -/
theorem single_heat_projection_hilbertSchmidt_tsum {ι : Type*} [Countable ι]
    {t : ℝ} (ht : 0 < t) (B : ι → CircleL2) :
    (∫⁻ x : HeatCircle, (∑' j, ENNReal.ofReal
      (‖(Submodule.span ℂ {circleHeat t x}).starProjection (B j)‖ ^ 2)) ∂haarAddCircle) ≤
      ENNReal.ofReal ((2 * t) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0) *
        ∑' j, ENNReal.ofReal (‖circleHeatOperator t ht.le (B j)‖ ^ 2) := by
  have hG : 0 < HeatTrace.fractionalGaussianIntegral 0 :=
    HeatTrace.fractionalGaussianIntegral_pos (by norm_num)
  rw [lintegral_tsum (fun j =>
    (single_heat_projection_integrable ht (B j)).aestronglyMeasurable.aemeasurable.ennreal_ofReal),
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  rw [← ofReal_integral_eq_lintegral_ofReal (single_heat_projection_integrable ht (B j))
    (ae_of_all _ (fun x => sq_nonneg _)), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (single_heat_projection_energy ht (B j))

theorem circleHeat_norm_sq_center (t : ℝ) (x y : HeatCircle) :
    ‖circleHeat t x‖ ^ 2 = ‖circleHeat t y‖ ^ 2 := by
  by_cases ht : 0 < t
  · have hx := hasSum_sq_fourierCoeff (circleHeat t x)
    have hy := hasSum_sq_fourierCoeff (circleHeat t y)
    rw [circle_spatial_energy_eq_norm_sq] at hx hy
    simp_rw [circleHeat_fourierCoeff ht, heatCoeff_norm_sq] at hx hy
    exact hx.unique hy
  · simp only [circleHeat, dite_eq_right ht]

/-- A genuine single point history with equal stopping and target age. -/
def pointHistory (t : ℝ) (x : HeatCircle) : ℝ → CircleL2 :=
  historyF ({()} : Finset Unit) (fun _ => 1) (fun _ => t) (fun _ => t) (fun _ => x)

def pointVariance (t : ℝ) : ℝ := (fullPhysicalEnergy (pointHistory t 0) 0).toReal

theorem pointHistory_current {t : ℝ} (ht : 0 < t) (x : HeatCircle) :
    pointHistory t x 0 = circleHeat t x := by
  simp only [pointHistory, historyF, Finset.sum_singleton, ite_eq_left ht, sub_zero, one_smul]

theorem pointHistory_energy_center (t : ℝ) (x : HeatCircle) :
    (fullPhysicalEnergy (pointHistory t x) 0).toReal = pointVariance t := by
  unfold pointVariance fullPhysicalEnergy
  congr 1
  apply lintegral_congr
  intro u
  simp only [circle_spatial_energy_eq_norm_sq, pointHistory, historyF, Finset.sum_singleton]
  split_ifs
  · simpa only [one_smul] using congrArg ENNReal.ofReal (circleHeat_norm_sq_center (t - u) x 0)
  · rfl

theorem pointVariance_lower {t : ℝ} (ht : 0 < t) :
    HeatTrace.fractionalGaussianIntegral 0 * (2 * t) ^ (-(1 / 2 : ℝ)) * (t / 2) ≤
      pointVariance t := by
  have hb := stopped_current_row_bound ({()} : Finset Unit) (fun _ => (1 : ℂ))
    (fun _ => t) (fun _ => t) (fun _ => (0 : HeatCircle)) (fun _ _ => le_rfl)
    (q := 0) ht (fun _ _ => by linarith)
  change ‖pointHistory t 0 0‖ ^ 2 ≤ (2 / t) * pointVariance t at hb
  rw [pointHistory_current ht] at hb
  have hl := (circleHeat_norm_sq_lower ht (0 : HeatCircle)).trans hb
  have hh := mul_le_mul_of_nonneg_right hl (show 0 ≤ t / 2 by positivity)
  convert hh using 1
  field_simp

theorem pointVariance_pos {t : ℝ} (ht : 0 < t) : 0 < pointVariance t := by
  apply lt_of_lt_of_le _ (pointVariance_lower ht)
  exact mul_pos (mul_pos (HeatTrace.fractionalGaussianIntegral_pos (by norm_num))
    (Real.rpow_pos_of_pos (by linarith) _)) (by positivity)

def pointMeanConstant : ℝ := 2 * (2 : ℝ) ^ (1 / 2 : ℝ) / HeatTrace.fractionalGaussianIntegral 0

theorem pointMeanConstant_pos : 0 < pointMeanConstant := by
  unfold pointMeanConstant
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num))

theorem pointVariance_inv_bound {t : ℝ} (ht : 0 < t) :
    (pointVariance t)⁻¹ ≤ pointMeanConstant * t ^ (-(1 / 2 : ℝ)) := by
  have hG : 0 < HeatTrace.fractionalGaussianIntegral 0 :=
    HeatTrace.fractionalGaussianIntegral_pos (by norm_num)
  have hhalf : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
  have htwo : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hpow : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← Real.rpow_mul_natCast ht.le, show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num,
      Real.rpow_one]
  have hm : 0 ≤ pointMeanConstant * t ^ (-(1 / 2 : ℝ)) := by
    exact mul_nonneg pointMeanConstant_pos.le (Real.rpow_nonneg ht.le _)
  have he := mul_le_mul_of_nonneg_left (pointVariance_lower ht) hm
  have hone : pointMeanConstant * t ^ (-(1 / 2 : ℝ)) *
      (HeatTrace.fractionalGaussianIntegral 0 * (2 * t) ^ (-(1 / 2 : ℝ)) * (t / 2)) = 1 := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le]
    simp only [pointMeanConstant, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg ht.le]
    field_simp
    nlinarith
  rw [hone] at he
  exact (inv_le_iff_one_le_mul₀ (pointVariance_pos ht)).mpr he

/-- The native one-point first-mean score bound with its actual stopped-history Gram.
Its input remains signed and is smoothed before the eventual second moment. -/
theorem native_point_mean_input {t : ℝ} (ht : 0 < t) (d : CircleL2) :
    (∫ x : HeatCircle, ‖inner ℂ (circleHeat t x) d‖ ^ 2 / pointVariance t ∂haarAddCircle) ≤
      pointMeanConstant * t ^ (-(1 / 2 : ℝ)) * ‖circleHeatOperator t ht.le d‖ ^ 2 := by
  rw [integral_div, heat_kernel_inner_energy ht d, div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (pointVariance_inv_bound ht)
    (sq_nonneg ‖circleHeatOperator t ht.le d‖)

/-- The damped native one-point mean row has the same signed-input bound. -/
theorem native_damped_point_mean_input {t Λ : ℝ} (ht : 0 < t) (hΛ : 0 ≤ Λ) (d : CircleL2) :
    (∫ x : HeatCircle, ‖inner ℂ ((Real.exp (-Λ * t) : ℂ) • circleHeat t x) d‖ ^ 2 /
      pointVariance t ∂haarAddCircle) ≤
      pointMeanConstant * t ^ (-(1 / 2 : ℝ)) * ‖circleHeatOperator t ht.le d‖ ^ 2 := by
  have he : ‖(Real.exp (-Λ * t) : ℂ)‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    apply Real.exp_le_one_iff.mpr
    have hp := mul_nonneg hΛ ht.le
    norm_num
    nlinarith
  simp_rw [inner_smul_left, norm_mul, Complex.norm_conj, mul_pow]
  have hi := native_point_mean_input ht d
  have hrewrite : (fun x : HeatCircle =>
      (‖(Real.exp (-Λ * t) : ℂ)‖ ^ 2 * ‖inner ℂ (circleHeat t x) d‖ ^ 2) / pointVariance t) =
      fun x => ‖(Real.exp (-Λ * t) : ℂ)‖ ^ 2 * (‖inner ℂ (circleHeat t x) d‖ ^ 2 / pointVariance t) := by
    funext x
    ring
  rw [hrewrite, integral_const_mul]
  have hnonneg : 0 ≤ ∫ x : HeatCircle, ‖inner ℂ (circleHeat t x) d‖ ^ 2 / pointVariance t ∂haarAddCircle :=
    integral_nonneg (fun _ => div_nonneg (sq_nonneg _) (pointVariance_pos ht).le)
  exact (mul_le_of_le_one_left hnonneg he).trans hi

/-- A connected adjacent age chain has the fixed ratio `A^m` after `m` links. -/
theorem adjacent_age_ratio_nat {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (age : ℕ → ℝ)
    (hstep : ∀ k < m, age (k + 1) ≤ A * age k) :
    ∀ k ≤ m, age k ≤ A ^ k * age 0 := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < m := by omega
    calc
      age (k + 1) ≤ A * age k := hstep k hk'
      _ ≤ A * (A ^ k * age 0) := mul_le_mul_of_nonneg_left (ih (by omega)) hA
      _ = A ^ (k + 1) * age 0 := by rw [pow_succ]; ring

theorem adjacent_age_ratio_fin {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (age : Fin (m + 1) → ℝ)
    (hstep : ∀ i : Fin m, age i.succ ≤ A * age i.castSucc) :
    age (Fin.last m) ≤ A ^ m * age 0 := by
  let a : ℕ → ℝ := fun k => age ⟨min k m, by omega⟩
  have ha : ∀ k < m, a (k + 1) ≤ A * a k := by
    intro k hk
    have hh := hstep ⟨k, hk⟩
    have h₁ : (⟨min (k + 1) m, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).succ :=
      Fin.ext (min_eq_left (by omega))
    have h₀ : (⟨min k m, by omega⟩ : Fin (m + 1)) = (⟨k, hk⟩ : Fin m).castSucc :=
      Fin.ext (min_eq_left hk.le)
    simpa only [a, h₁, h₀] using hh
  have hh := adjacent_age_ratio_nat hA a ha m le_rfl
  have h₁ : (⟨min m m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (min_self m)
  have h₀ : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext (min_eq_left (Nat.zero_le m))
  simpa only [a, h₁, h₀] using hh

/-- Separation of consecutive age groups gives every pair required by the frame. -/
theorem adjacent_group_separation {A : ℝ} (hA : 1 ≤ A) {m : ℕ}
    (lower upper : Fin (m + 1) → ℝ) (hlo : ∀ g, 0 ≤ lower g)
    (hlohi : ∀ g, lower g ≤ upper g)
    (hstep : ∀ i : Fin m, A * upper i.castSucc ≤ lower i.succ) :
    ∀ g h : Fin (m + 1), g < h → A * upper g ≤ lower h := by
  have hmon : Monotone lower := Fin.monotone_iff_le_succ.mpr (by
    intro i
    exact (hlohi i.castSucc).trans ((le_mul_of_one_le_left
      ((hlo i.castSucc).trans (hlohi i.castSucc)) hA).trans (hstep i)))
  intro g h hgh
  let i : Fin m := ⟨g.val, by have hh := h.isLt; change g.val < h.val at hgh; omega⟩
  have hig : i.castSucc = g := Fin.ext rfl
  have hih : i.succ ≤ h := by change g.val + 1 ≤ h.val; exact hgh
  rw [← hig]
  exact (hstep i).trans (hmon hih)

/-- The manuscript's chosen separation `A>16n²` implies the proved frame threshold. -/
theorem manuscript_age_separation_threshold {n : ℕ} (hn : 0 < n) {A : ℝ}
    (hA : 16 * (n : ℝ) ^ 2 < A) : 4 * (n : ℝ) ^ 2 + 1 ≤ A := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- Covariance domination is used only as a quadratic-form inequality; no inverse
or nondegeneracy of the observation covariance is required. -/
theorem range_factorization_of_gram_dominance {D G E : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : D →ₗ[ℂ] G) (B : D →ₗ[ℂ] E) [CompleteSpace C.range]
    (energy : D → ℝ) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hB : ∀ z, ‖B z‖ ^ 2 ≤ K ^ 2 * energy z)
    (hcov : ∀ z, c * energy z ≤ ‖C z‖ ^ 2) :
    ∃ T : G →L[ℂ] E, ‖T‖ ≤ K / Real.sqrt c ∧ (∀ z, T (C z) = B z) ∧
      T = T.comp C.range.starProjection := by
  apply range_factorization_of_bound C B (div_nonneg hK (Real.sqrt_nonneg _))
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, div_pow, Real.sq_sqrt hc.le]
  have he : energy z ≤ ‖C z‖ ^ 2 / c :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcov z)
  calc
    ‖B z‖ ^ 2 ≤ K ^ 2 * energy z := hB z
    _ ≤ K ^ 2 * (‖C z‖ ^ 2 / c) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by ring

/-- The true undamped current row factors through any covariance representation
which dominates the original stopped-history Gram. -/
theorem current_covariance_range_factorization {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {q δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hstop : ∀ i ∈ I, q + δ ≤ σ i) (C : (ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (historyF I z σ target center) q).toReal ≤ ‖C z‖ ^ 2) :
    ∃ T : G →L[ℂ] CircleL2, ‖T‖ ≤ Real.sqrt (2 / δ) / Real.sqrt c ∧
      (∀ z, T (C z) = historyF I z σ target center q) ∧ T = T.comp C.range.starProjection := by
  apply range_factorization_of_gram_dominance C (currentLinearMap I σ target center q)
    (fun z => (fullPhysicalEnergy (historyF I z σ target center) q).toReal) hc (Real.sqrt_nonneg _)
    _ hcov
  intro z
  rw [Real.sq_sqrt (show 0 ≤ 2 / δ by positivity)]
  exact stopped_current_row_bound I z σ target center hages hδ hstop

/-- The true damped row factors through the original covariance, with no
coordinatewise damping of an inverse Gram matrix. -/
theorem damped_current_covariance_range_factorization {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {Λ q δ c : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (hc : 0 < c)
    (hstop : ∀ i ∈ I, q + δ ≤ σ i) (C : (ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (historyF I z σ target center) q).toReal ≤ ‖C z‖ ^ 2) :
    ∃ T : G →L[ℂ] CircleL2, ‖T‖ ≤ Real.sqrt (2 / δ) / Real.sqrt c ∧
      (∀ z, T (C z) = historyG I z σ target center Λ q) ∧ T = T.comp C.range.starProjection := by
  apply range_factorization_of_gram_dominance C (dampedCurrentLinearMap I σ target center Λ q)
    (fun z => (fullPhysicalEnergy (historyF I z σ target center) q).toReal) hc (Real.sqrt_nonneg _)
    _ hcov
  intro z
  rw [Real.sq_sqrt (show 0 ≤ 2 / δ by positivity)]
  exact stopped_damped_current_row_bound I z σ target center hages hΛ hδ hstop

/-- The covariance-normalized defect row retains its clipped mass factor for
every actual covariance dominating a fixed fraction of the original Gram. -/
theorem defect_current_covariance_range_factorization {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {Λ q w M c : ℝ}
    (hΛ : 0 < Λ) (hw : 0 < w) (hM : 1 ≤ M) (hc : 0 < c)
    (hlower : ∀ i ∈ I, q + w ≤ σ i) (hupper : ∀ i ∈ I, σ i ≤ q + M * w)
    (C : (ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (historyF I z σ target center) q).toReal ≤ ‖C z‖ ^ 2) :
    ∃ T : G →L[ℂ] CircleL2,
      ‖T‖ ≤ (Real.sqrt (max M 8 / w) * min 1 (Λ * w)) / Real.sqrt c ∧
      (∀ z, T (C z) = historyF I z σ target center q - historyG I z σ target center Λ q) ∧
      T = T.comp C.range.starProjection := by
  have hr : 0 ≤ min 1 (Λ * w) := le_min (by norm_num) (mul_nonneg hΛ.le hw.le)
  have hmax : 0 ≤ max M 8 := by linarith [le_max_right M 8]
  have hscale : 0 ≤ max M 8 / w := div_nonneg hmax hw.le
  apply range_factorization_of_gram_dominance C
    (currentLinearMap I σ target center q - dampedCurrentLinearMap I σ target center Λ q)
    (fun z => (fullPhysicalEnergy (historyF I z σ target center) q).toReal) hc
    (mul_nonneg (Real.sqrt_nonneg _) hr) _ hcov
  intro z
  rw [mul_pow, Real.sq_sqrt hscale]
  change ‖historyF I z σ target center q - historyG I z σ target center Λ q‖ ^ 2 ≤ _
  have hb := stopped_current_difference_clipped I z σ target center hages hΛ hw hM hlower hupper
  convert hb using 1
  ring

/-- A dominating covariance representation continuously recovers the original
history feature vector on the actual covariance range. -/
theorem covariance_range_embedding {D G H : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (C : D →ₗ[ℂ] G) (A : D →ₗ[ℂ] H) [CompleteSpace C.range] {c : ℝ} (hc : 0 < c)
    (hcov : ∀ z, c * ‖A z‖ ^ 2 ≤ ‖C z‖ ^ 2) :
    ∃ U : G →L[ℂ] H, ‖U‖ ≤ 1 / Real.sqrt c ∧ (∀ z, U (C z) = A z) ∧
      U = U.comp C.range.starProjection := by
  apply range_factorization_of_gram_dominance C A (fun z => ‖A z‖ ^ 2) hc
    (show (0 : ℝ) ≤ 1 by norm_num) _ hcov
  intro z
  simp only [one_pow, one_mul, le_refl]

/-- A damped row keeps its right heat factor after normalization by any actual
covariance dominating the original stopped-history Gram. -/
theorem damped_covariance_heat_factorization {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {Λ q δ c : ℝ}
    (hΛ : 0 < Λ) (hδ : 0 < δ) (hc : 0 < c)
    (hstop : ∀ i ∈ I, q + δ ≤ σ i) (C : (ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (historyF I z σ target center) q).toReal ≤ ‖C z‖ ^ 2) :
    ∃ T : G →L[ℂ] CircleL2, ‖T‖ ≤ Real.sqrt (4 / δ) / Real.sqrt c ∧
      (∀ z, historyG I z σ target center Λ q = (Real.exp (-Λ * (δ / 2)) : ℂ) •
        circleHeatOperator (δ / 2) (by positivity) (T (C z))) ∧
      T = T.comp C.range.starProjection := by
  obtain ⟨U, hU, hUapply, hUproj⟩ := covariance_range_embedding C
    (historyLinearMap I σ target center hages q) hc (by
      intro z
      change c * ‖historyTimeVector I z σ target center hages q‖ ^ 2 ≤ _
      rw [historyTimeVector_norm_sq]
      exact hcov z)
  obtain ⟨S, hS, hSapply, _⟩ := damped_current_history_heat_factorization
    I σ target center hages hΛ hδ hstop
  refine ⟨S.comp U, ?_, ?_, ?_⟩
  · calc
      ‖S.comp U‖ ≤ ‖S‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.sqrt (4 / δ) * (1 / Real.sqrt c) :=
        mul_le_mul hS hU (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · intro z
    have hu : U (C z) = historyTimeVector I z σ target center hages q := hUapply z
    simpa only [ContinuousLinearMap.comp_apply, hu] using hSapply z
  · apply ContinuousLinearMap.ext
    intro x
    exact congrArg S (congrArg (fun V : G →L[ℂ] Lp CircleL2 2 (volume.restrict (Ici q)) => V x) hUproj)

/-- The full all-age clipped score row can be normalized against a dominating
covariance, with its actual global history and its clipped mass factor retained. -/
theorem separated_group_covariance_defect_factorization {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] {n : ℕ} (hn : 0 < n)
    (I : Fin n → Finset ι) (σ target : Fin n → ι → ℝ)
    (center : Fin n → ι → HeatCircle) (hages : ∀ g, ∀ i ∈ I g, σ g i ≤ target g i)
    (lower upper : Fin n → ℝ) {Λ q A M c : ℝ} (hΛ : 0 < Λ) (hc : 0 < c)
    (hA : 4 * (n : ℝ) ^ 2 + 1 ≤ A) (hM : 1 ≤ M)
    (hlo : ∀ g, 0 < lower g) (hlohi : ∀ g, lower g ≤ upper g)
    (hcompare : ∀ g, upper g ≤ M * lower g)
    (hstlo : ∀ g, ∀ i ∈ I g, q + lower g ≤ σ g i)
    (hsthi : ∀ g, ∀ i ∈ I g, σ g i ≤ q + upper g)
    (hsep : ∀ g h, g < h → A * upper g ≤ lower h)
    (C : (Fin n → ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (fun u => ∑ g : Fin n,
      historyF (I g) (z g) (σ g) (target g) (center g) u) q).toReal ≤ ‖C z‖ ^ 2)
    (g : Fin n) :
    ∃ T : G →L[ℂ] CircleL2,
      ‖T‖ ≤ (Real.sqrt (2 * max M 8 / lower g) * min 1 (Λ * lower g)) / Real.sqrt c ∧
      (∀ z, T (C z) = historyF (I g) (z g) (σ g) (target g) (center g) q -
        historyG (I g) (z g) (σ g) (target g) (center g) Λ q) ∧
      T = T.comp C.range.starProjection := by
  obtain ⟨U, hU, hUapply, hUproj⟩ := covariance_range_embedding C
    (groupedHistoryLinearMap I σ target center hages q) hc (by
      intro z
      rw [groupedHistoryLinearMap_norm_sq]
      exact hcov z)
  obtain ⟨S, hS, hSapply, _⟩ := separated_group_defect_range_factorization hn
    I σ target center hages lower upper hΛ hA hM hlo hlohi hcompare hstlo hsthi hsep g
  have hr : 0 ≤ min 1 (Λ * lower g) := le_min (by norm_num) (mul_nonneg hΛ.le (hlo g).le)
  refine ⟨S.comp U, ?_, ?_, ?_⟩
  · calc
      ‖S.comp U‖ ≤ ‖S‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (Real.sqrt (2 * max M 8 / lower g) * min 1 (Λ * lower g)) * (1 / Real.sqrt c) :=
        mul_le_mul hS hU (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)
      _ = _ := by ring
  · intro z
    simpa only [ContinuousLinearMap.comp_apply, hUapply] using hSapply z
  · apply ContinuousLinearMap.ext
    intro x
    exact congrArg S (congrArg (fun V : G →L[ℂ] Lp CircleL2 2 (volume.restrict (Ici q)) => V x) hUproj)

/-- A bounded covariance-range map has a Riesz representative inside the actual
covariance range, even when that covariance has a kernel. -/
theorem range_adjoint_representer {G E : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K : Submodule ℂ G) [CompleteSpace K] (T : G →L[ℂ] E) (d : E) :
    ∃ m ∈ K, (∀ y ∈ K, inner ℂ y m = inner ℂ (T y) d) ∧ ‖m‖ ≤ ‖T‖ * ‖d‖ := by
  let m : G := K.starProjection (ContinuousLinearMap.adjoint T d)
  refine ⟨m, (K.orthogonalProjectionOnto _).property, ?_, ?_⟩
  · intro y hy
    change inner ℂ y (K.starProjection (ContinuousLinearMap.adjoint T d)) = _
    rw [← K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr hy,
      ContinuousLinearMap.adjoint_inner_right]
  · calc
      ‖m‖ ≤ ‖ContinuousLinearMap.adjoint T d‖ := K.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖d‖ := (ContinuousLinearMap.adjoint T).le_opNorm d
      _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]

/-- The genuine damped first-mean score has a representative in the actual
covariance range, with the right heat factor retained on its signed input. -/
theorem damped_covariance_mean_representer {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (I : Finset ι) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i ∈ I, σ i ≤ target i) {Λ q δ c : ℝ}
    (hΛ : 0 < Λ) (hδ : 0 < δ) (hc : 0 < c)
    (hstop : ∀ i ∈ I, q + δ ≤ σ i) (C : (ι → ℂ) →ₗ[ℂ] G)
    (hcov : ∀ z, c * (fullPhysicalEnergy (historyF I z σ target center) q).toReal ≤ ‖C z‖ ^ 2)
    (d : CircleL2) :
    ∃ m ∈ C.range, (∀ z, inner ℂ (C z) m = inner ℂ (historyG I z σ target center Λ q) d) ∧
      ‖m‖ ≤ (Real.sqrt (4 / δ) / Real.sqrt c) *
        ‖circleHeatOperator (δ / 2) (by positivity) d‖ := by
  obtain ⟨T, hT, hTapply, _⟩ := damped_covariance_heat_factorization
    I σ target center hages hΛ hδ hc hstop C hcov
  let d' : CircleL2 := (Real.exp (-Λ * (δ / 2)) : ℂ) •
    circleHeatOperator (δ / 2) (by positivity) d
  obtain ⟨m, hm, hpair, hnorm⟩ := range_adjoint_representer C.range T d'
  refine ⟨m, hm, ?_, ?_⟩
  · intro z
    rw [hpair _ (LinearMap.mem_range_self C z), hTapply z]
    simp only [d', inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      circleHeatOperator_self_adjoint]
  · have hs : ‖(Real.exp (-Λ * (δ / 2)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have hh := mul_nonneg hΛ.le (show 0 ≤ δ / 2 by positivity)
      linarith
    have hd : ‖d'‖ ≤ ‖circleHeatOperator (δ / 2) (show 0 ≤ δ / 2 by positivity) d‖ := by
      dsimp only [d']
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    exact hnorm.trans (mul_le_mul hT hd (norm_nonneg _)
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- The physical cross-kernel with its genuine relative-center Fourier phases. -/
def heatCrossKernel (t : ℝ) (x y : HeatCircle) : ℂ :=
  ∑' n : ℤ, (Real.exp (-t * (n : ℝ) ^ 2) : ℂ) * fourier n x * fourier (-n) y

theorem circleHeat_cross_gram {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : HeatCircle) :
    inner ℂ (circleHeat a x) (circleHeat b y) = heatCrossKernel (a + b) x y := by
  have hh := (heat_kernel_inner_hasSum ha x (circleHeat b y)).tsum_eq
  rw [← hh]
  unfold heatCrossKernel
  apply tsum_congr
  intro n
  rw [circleHeat_fourierCoeff hb]
  simp only [heatCoeff]
  have he : Real.exp (-(a + b) * (n : ℝ) ^ 2) =
      Real.exp (-a * (n : ℝ) ^ 2) * Real.exp (-b * (n : ℝ) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Complex.ofReal_mul]
  ring

def singleStoppedHistory (σ target : ℝ) (x : HeatCircle) : ℝ → CircleL2 :=
  historyF ({()} : Finset Unit) (fun _ => 1) (fun _ => σ) (fun _ => target) (fun _ => x)

theorem singleStoppedHistory_apply (σ target : ℝ) (x : HeatCircle) (u : ℝ) :
    singleStoppedHistory σ target x u = if u < σ then circleHeat (target - u) x else 0 := by
  simp only [singleStoppedHistory, historyF, Finset.sum_singleton, one_smul]

theorem single_stopped_covariance_kernel {σ τ T U q : ℝ} (hT : σ ≤ T) (hU : τ ≤ U)
    (x y : HeatCircle) :
    historyPairing (singleStoppedHistory σ T x) (singleStoppedHistory τ U y) q =
      ∫ u in Ioc q (min σ τ), heatCrossKernel (T + U - 2 * u) x y := by
  unfold historyPairing
  have he : (fun u => inner ℂ (singleStoppedHistory σ T x u) (singleStoppedHistory τ U y u)) =
      (Iio (min σ τ)).indicator (fun u => heatCrossKernel (T + U - 2 * u) x y) := by
    funext u
    rw [singleStoppedHistory_apply, singleStoppedHistory_apply]
    by_cases hu : u < min σ τ
    · have hσ : u < σ := lt_of_lt_of_le hu (min_le_left _ _)
      have hτ : u < τ := lt_of_lt_of_le hu (min_le_right _ _)
      rw [ite_eq_left hσ, ite_eq_left hτ, Set.indicator_of_mem (s := Iio (min σ τ)) hu,
        circleHeat_cross_gram (by linarith : 0 < T - u) (by linarith : 0 < U - u)]
      congr 1
      ring
    · rw [Set.indicator_of_notMem (s := Iio (min σ τ)) hu]
      by_cases hσ : u < σ
      · have hτ : ¬u < τ := by exact fun h => hu (lt_min hσ h)
        rw [ite_eq_left hσ, ite_eq_right hτ, inner_zero_right]
      · rw [ite_eq_right hσ, inner_zero_left]
  rw [he, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    show Iio (min σ τ) ∩ Ici q = Ico q (min σ τ) by ext u; simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_Ico, and_comm],
    integral_Ico_eq_integral_Ioc]

def stoppedObservationFeature (σ target : ℝ) (x : HeatCircle) (hage : σ ≤ target) (q : ℝ) :
    Lp CircleL2 2 (volume.restrict (Ici q)) :=
  historyTimeVector ({()} : Finset Unit) (fun _ => 1) (fun _ => σ) (fun _ => target)
    (fun _ => x) (fun _ _ => hage) q

/-- The actual stopped-history covariance matrix is its time/spatial L² Gram. -/
def stoppedCovariance {ι : Type*} (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (i j : ι) : ℂ :=
  inner ℂ (stoppedObservationFeature (σ i) (target i) (center i) (hages i) q)
    (stoppedObservationFeature (σ j) (target j) (center j) (hages j) q)

theorem stoppedCovariance_kernel {ι : Type*} (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (i j : ι) :
    stoppedCovariance σ target center hages q i j = ∫ u in Ioc q (min (σ i) (σ j)),
      heatCrossKernel (target i + target j - 2 * u) (center i) (center j) := by
  unfold stoppedCovariance stoppedObservationFeature historyTimeVector
  rw [toLp_inner_eq_integral]
  exact single_stopped_covariance_kernel (hages i) (hages j) _ _

theorem stoppedCovariance_hermitian {ι : Type*} (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (i j : ι) :
    (starRingEnd ℂ) (stoppedCovariance σ target center hages q j i) =
      stoppedCovariance σ target center hages q i j := inner_conj_symm _ _

theorem history_vector_sum_features {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    historyTimeVector Finset.univ z σ target center (fun i _ => hages i) q =
      ∑ i, z i • stoppedObservationFeature (σ i) (target i) (center i) (hages i) q := by
  let H : ι → ℝ → CircleL2 := fun i => singleStoppedHistory (σ i) (target i) (center i)
  have hm : ∀ i, MemLp (H i) 2 (volume.restrict (Ici q)) := by
    intro i
    exact historyF_memLp_time ({()} : Finset Unit) (fun _ => 1) (fun _ => σ i)
      (fun _ => target i) (fun _ => center i) (fun _ _ => hages i) q
  have he : historyF Finset.univ z σ target center = fun u => ∑ i, z i • H i u := by
    funext u
    simp only [historyF, H, singleStoppedHistory_apply]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp only [smul_zero]
  have hprod : ∀ i, MemLp (fun u => z i • H i u) 2 (volume.restrict (Ici q)) :=
    fun i => (hm i).const_smul (z i)
  unfold historyTimeVector
  have htoLp := MemLp.toLp_congr
    (historyF_memLp_time Finset.univ z σ target center (fun i _ => hages i) q)
    (memLp_finsetSum Finset.univ (fun i _ => hprod i)) (Filter.Eventually.of_forall (congrFun he))
  rw [toLp_finsetSum Finset.univ _ hprod] at htoLp
  refine htoLp.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact MemLp.toLp_const_smul (z i) (hm i)

/-- The concrete covariance quadratic form is exactly the energy of the full
original signed physical history, with no conditioning or collision restriction. -/
theorem stoppedCovariance_quadratic {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    (∑ i, ∑ j, (starRingEnd ℂ) (z i) * stoppedCovariance σ target center hages q i j * z j) =
      ((fullPhysicalEnergy (historyF Finset.univ z σ target center) q).toReal : ℂ) := by
  let v : ι → Lp CircleL2 2 (volume.restrict (Ici q)) := fun i =>
    stoppedObservationFeature (σ i) (target i) (center i) (hages i) q
  have he : inner ℂ (∑ i, z i • v i) (∑ j, z j • v j) =
      ∑ i, ∑ j, (starRingEnd ℂ) (z i) * stoppedCovariance σ target center hages q i j * z j := by
    rw [sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    change (starRingEnd ℂ) (z i) * (z j * inner ℂ (v i) (v j)) =
      (starRingEnd ℂ) (z i) * inner ℂ (v i) (v j) * z j
    ring
  rw [← he]
  have hv : (∑ i, z i • v i) =
      historyTimeVector Finset.univ z σ target center (fun i _ => hages i) q :=
    (history_vector_sum_features z σ target center hages q).symm
  rw [hv, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    historyTimeVector_norm_sq]
  rfl

theorem stoppedCovariance_cross_form {ι : Type*} [Fintype ι]
    (z w : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    (∑ i, ∑ j, (starRingEnd ℂ) (z i) * stoppedCovariance σ target center hages q i j * w j) =
      historyPairing (historyF Finset.univ z σ target center)
        (historyF Finset.univ w σ target center) q := by
  unfold historyPairing
  rw [← toLp_inner_eq_integral
    (historyF_memLp_time Finset.univ z σ target center (fun i _ => hages i) q)
    (historyF_memLp_time Finset.univ w σ target center (fun i _ => hages i) q)]
  change _ = inner ℂ (historyTimeVector Finset.univ z σ target center (fun i _ => hages i) q)
    (historyTimeVector Finset.univ w σ target center (fun i _ => hages i) q)
  rw [history_vector_sum_features, history_vector_sum_features, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold stoppedCovariance
  ring

/-- Positivity of the actual covariance quadratic form follows from the full
physical history energy, including arbitrary collisions and covariance kernels. -/
theorem stoppedCovariance_positive {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (z i) * stoppedCovariance σ target center hages q i j * z j).re := by
  rw [stoppedCovariance_quadratic]
  exact ENNReal.toReal_nonneg

theorem stoppedCovariance_kernel_iff {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    (∑ i, ∑ j, (starRingEnd ℂ) (z i) * stoppedCovariance σ target center hages q i j * z j) = 0 ↔
      historyTimeVector Finset.univ z σ target center (fun i _ => hages i) q = 0 := by
  rw [stoppedCovariance_quadratic, ← historyTimeVector_norm_sq Finset.univ z σ target center (fun i _ => hages i) q,
    Complex.ofReal_eq_zero, sq_eq_zero_iff, norm_eq_zero]

/-- Every actual covariance-kernel direction annihilates both original and
damped current rows. The proof uses full histories, including all collisions. -/
theorem current_rows_annihilate_covariance_kernel {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (σ target : ι → ℝ) (center : ι → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) {Λ q δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ)
    (hstop : ∀ i, q + δ ≤ σ i)
    (hz : (∑ i, ∑ j, (starRingEnd ℂ) (z i) * stoppedCovariance σ target center hages q i j * z j) = 0) :
    historyF Finset.univ z σ target center q = 0 ∧
      historyG Finset.univ z σ target center Λ q = 0 := by
  have hv := (stoppedCovariance_kernel_iff z σ target center hages q).mp hz
  obtain ⟨T, _, hT, _⟩ := current_history_range_factorization Finset.univ σ target center
    (fun i _ => hages i) hδ (fun i _ => hstop i)
  obtain ⟨U, _, hU, _⟩ := damped_current_history_range_factorization Finset.univ σ target center
    (fun i _ => hages i) hΛ hδ (fun i _ => hstop i)
  constructor
  · rw [← hT z, hv, map_zero]
  · rw [← hU z, hv, map_zero]

theorem historyF_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (z : ι → κ → ℂ) (σ target : ι → κ → ℝ) (center : ι → κ → HeatCircle) :
    historyF Finset.univ (fun p : ι × κ => z p.1 p.2)
      (fun p => σ p.1 p.2) (fun p => target p.1 p.2) (fun p => center p.1 p.2) =
      fun u => ∑ g, historyF Finset.univ (z g) (σ g) (target g) (center g) u := by
  funext u
  simp only [historyF, Fintype.sum_prod_type]

/-- The all-age block-diagonal covariance frame for the concrete physical Gram
matrix, at the separation threshold used in the manuscript. -/
theorem stoppedCovariance_block_frame {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (z : Fin n → ι → ℂ) (σ target : Fin n → ι → ℝ) (center : Fin n → ι → HeatCircle)
    (hages : ∀ g i, σ g i ≤ target g i) (lower upper : Fin n → ℝ) {q A : ℝ}
    (hA : 16 * (n : ℝ) ^ 2 < A) (hlo : ∀ g, 0 < lower g) (hlohi : ∀ g, lower g ≤ upper g)
    (hstlo : ∀ g i, q + lower g ≤ σ g i) (hsthi : ∀ g i, σ g i ≤ q + upper g)
    (hsep : ∀ g h, g < h → A * upper g ≤ lower h) :
    (1 / 2 : ℝ) * (∑ g : Fin n,
      (∑ i, ∑ j, (starRingEnd ℂ) (z g i) *
        stoppedCovariance (σ g) (target g) (center g) (hages g) q i j * z g j).re) ≤
      (∑ p : Fin n × ι, ∑ r : Fin n × ι,
        (starRingEnd ℂ) (z p.1 p.2) *
          stoppedCovariance (fun p => σ p.1 p.2) (fun p => target p.1 p.2)
            (fun p => center p.1 p.2) (fun p => hages p.1 p.2) q p r * z r.1 r.2).re := by
  simp_rw [stoppedCovariance_quadratic, Complex.ofReal_re]
  rw [historyF_prod]
  exact separated_history_covariance_frame hn (fun _ => Finset.univ) z σ target center
    (fun g i _ => hages g i) lower upper (manuscript_age_separation_threshold hn hA)
    hlo hlohi (fun g i _ => hstlo g i) (fun g i _ => hsthi g i) hsep

end SHE.StoppedFourier
