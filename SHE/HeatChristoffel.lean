module

public import SHE.HeatProjection
public import SHE.HistoryFrames

/-! Actual continuous evaluation on finite physical heat spans, and its
collision-uniform covariance-range factorization. No inverse Gram matrix is
used, so coincident observations and singular covariances are allowed. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatChristoffel
open MeasureTheory Set Real AddCircle SHE.HeatTorus SHE.HeatTorusKernel
  SHE.HeatProjection
open scoped InnerProductSpace

variable {q : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle)
  (ht : ∀ i, 0 < t i)

include ht in
theorem exists_continuous_heat_representative (f : heatSpan t a) :
    ∃ P : C(UnitAddCircle, ℂ), ContinuousMap.toLp 2 haarAddCircle ℂ P = (f : CircleL2) := by
  obtain ⟨c, b, F, hF, _, _, htrans⟩ := exists_cut_line_lift q t a ht f f.property
  exact ⟨continuousTranslate c (SHE.HeatPeriodization.circlePeriodize t b ht F hF),
    (toLp_continuousTranslate c _).trans htrans⟩

/-- The unique continuous representative, as an actual linear lifting of
the physical finite-dimensional L² subspace. -/
def continuousLift : heatSpan t a →ₗ[ℂ] C(UnitAddCircle, ℂ) where
  toFun f := Classical.choose (exists_continuous_heat_representative t a ht f)
  map_add' f g := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) haarAddCircle
    rw [map_add]
    simp only [Classical.choose_spec (exists_continuous_heat_representative t a ht _)]
    rfl
  map_smul' c f := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) haarAddCircle
    rw [map_smul]
    simp only [Classical.choose_spec (exists_continuous_heat_representative t a ht _)]
    rfl

theorem toLp_continuousLift (f : heatSpan t a) :
    ContinuousMap.toLp 2 haarAddCircle ℂ (continuousLift t a ht f) = (f : CircleL2) :=
  Classical.choose_spec (exists_continuous_heat_representative t a ht f)

def evaluation (x : UnitAddCircle) : heatSpan t a →ₗ[ℂ] ℂ where
  toFun f := continuousLift t a ht f x
  map_add' f g := by simp only [map_add, ContinuousMap.add_apply]
  map_smul' c f := by simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul,
    RingHom.id_apply]

theorem continuousLift_eq_of_toLp (f : heatSpan t a) (P : C(UnitAddCircle, ℂ))
    (hP : ContinuousMap.toLp 2 haarAddCircle ℂ P = (f : CircleL2)) :
    continuousLift t a ht f = P := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) haarAddCircle
  exact (toLp_continuousLift t a ht f).trans hP.symm

/-- The Christoffel estimate is an evaluation bound on the literal physical
heat subspace, with its genuine continuous representative. -/
theorem finite_heat_evaluation_bound (q : ℕ) :
    ∃ h C : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) → ∀ (f : heatSpan t a) (x : UnitAddCircle),
      ‖evaluation t a ht x f‖ ^ 2 ≤
        C * ‖f‖ ^ 2 * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, C, hh, hh1, hC, henv⟩ :=
    SHE.GlobalTorusHeatSpan.finite_torus_heat_span_envelope q
  refine ⟨h, C, hh, hh1, hC, ?_⟩
  intro t a ht hth f x
  obtain ⟨P, hP, hpoint⟩ := henv t a ht hth f f.property
  change ‖continuousLift t a ht f x‖ ^ 2 ≤ _
  rw [continuousLift_eq_of_toLp t a ht f P hP]
  exact hpoint x

def evaluationContinuous (x : UnitAddCircle) : heatSpan t a →L[ℂ] ℂ :=
  (evaluation t a ht x).toContinuousLinearMap

theorem evaluationContinuous_apply (x : UnitAddCircle) (f : heatSpan t a) :
    evaluationContinuous t a ht x f = evaluation t a ht x f := rfl

theorem norm_evaluationContinuous_le {A : ℝ} (hA : 0 ≤ A) (x : UnitAddCircle)
    (hbound : ∀ f : heatSpan t a, ‖evaluation t a ht x f‖ ^ 2 ≤ A * ‖f‖ ^ 2) :
    ‖evaluationContinuous t a ht x‖ ≤ sqrt A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sqrt_nonneg _)
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, sq_sqrt hA]
  exact hbound f

/-- Bessel's inequality for a genuine bounded complex functional. This is
the finite Christoffel sum, with no loss depending on the frame cardinality. -/
theorem sum_sq_functional_le {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : H →L[ℂ] ℂ) (e : I → H) (he : Orthonormal ℂ e) :
    ∑ i, ‖L (e i)‖ ^ 2 ≤ ‖L‖ ^ 2 := by
  let y := (InnerProductSpace.toDual ℂ H).symm L
  have hy (v : H) : inner ℂ y v = L v := by
    exact congrArg (fun F : H →L[ℂ] ℂ => F v)
      ((InnerProductSpace.toDual ℂ H).apply_symm_apply L)
  have hn : ‖y‖ = ‖L‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map L
  calc
    _ = ∑ i, ‖inner ℂ (e i) y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hy, norm_inner_symm]
    _ ≤ ‖y‖ ^ 2 := by simpa using he.sum_inner_products_le y (s := Finset.univ)
    _ = _ := by rw [hn]

/-- The physical heat Christoffel kernel is bounded uniformly through all
collisions and all age ratios. The orthonormal frame can be any subframe of
the true heat span. -/
theorem finite_heat_christoffel_bound (q : ℕ) :
    ∃ h C : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) → ∀ (r : ℕ) (e : Fin r → heatSpan t a), Orthonormal ℂ e →
      ∀ x : UnitAddCircle,
      ∑ i, ‖evaluation t a ht x (e i)‖ ^ 2 ≤
        C * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, C, hh, hh1, hC, hbound⟩ := finite_heat_evaluation_bound q
  refine ⟨h, C, hh, hh1, hC, ?_⟩
  intro t a ht hth r e he x
  have hW : 0 ≤ C * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
    apply mul_nonneg hC.le
    apply Finset.sum_nonneg
    intro i _
    unfold SHE.GlobalTorusHeatSpan.weight
    positivity
  have hL := norm_evaluationContinuous_le t a ht hW x (fun f => by
    convert! hbound t a ht hth f x using 1; ring)
  calc
    _ ≤ ‖evaluationContinuous t a ht x‖ ^ 2 :=
      sum_sq_functional_le (evaluationContinuous t a ht x) e he
    _ ≤ (sqrt (C * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x)) ^ 2 := by
      nlinarith [norm_nonneg (evaluationContinuous t a ht x),
        sqrt_nonneg (C * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x)]
    _ = _ := sq_sqrt hW

/-- A physical evaluation factors through any covariance dominating the
actual spatial heat Gram. This is a quotient/range construction and remains
valid for a singular observation covariance. -/
theorem covariance_evaluation_factorization {D G : Type*}
    [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (S : D →ₗ[ℂ] heatSpan t a) (C : D →ₗ[ℂ] G) [CompleteSpace C.range]
    {c W : ℝ} (hc : 0 < c) (hW : 0 ≤ W) (x : UnitAddCircle)
    (heval : ∀ f : heatSpan t a, ‖evaluation t a ht x f‖ ^ 2 ≤ W * ‖f‖ ^ 2)
    (hcov : ∀ z, c * ‖S z‖ ^ 2 ≤ ‖C z‖ ^ 2) :
    ∃ T : G →L[ℂ] ℂ, ‖T‖ ≤ sqrt W / sqrt c ∧
      (∀ z, T (C z) = evaluation t a ht x (S z)) ∧
      T = T.comp C.range.starProjection := by
  apply SHE.StoppedFourier.range_factorization_of_gram_dominance C
    ((evaluation t a ht x).comp S) (fun z => ‖S z‖ ^ 2) hc (sqrt_nonneg _) _ hcov
  intro z
  rw [sq_sqrt hW]
  exact heval (S z)

/-- A literal covariance-normalized physical row is represented by a vector
in the actual covariance range. Its squared norm has the collision-uniform
positive heat envelope; no inverse or pseudoinverse is postulated. -/
theorem finite_heat_covariance_score_bound (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) →
      ∀ {D G : Type*} [AddCommGroup D] [Module ℂ D]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (S : D →ₗ[ℂ] heatSpan t a) (C : D →ₗ[ℂ] G) [CompleteSpace C.range]
      (c : ℝ), 0 < c → (∀ z, c * ‖S z‖ ^ 2 ≤ ‖C z‖ ^ 2) →
      ∀ x : UnitAddCircle, ∃ m ∈ C.range,
      (∀ z, inner ℂ (C z) m = star (evaluation t a ht x (S z))) ∧
      ‖m‖ ^ 2 ≤ (K / c) * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, heval⟩ := finite_heat_evaluation_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro t a ht hth D G _ _ _ _ _ S C _ c hc hcov x
  let W := K * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x
  have hW : 0 ≤ W := by
    dsimp only [W]
    apply mul_nonneg hK.le
    apply Finset.sum_nonneg
    intro i _
    unfold SHE.GlobalTorusHeatSpan.weight
    positivity
  have hbound (f : heatSpan t a) : ‖evaluation t a ht x f‖ ^ 2 ≤ W * ‖f‖ ^ 2 := by
    convert! heval t a ht hth f x using 1; dsimp only [W]; ring
  obtain ⟨T, hT, hTC, _⟩ := covariance_evaluation_factorization t a ht S C hc hW x hbound hcov
  obtain ⟨m, hm, hpair, hn⟩ := SHE.StoppedFourier.range_adjoint_representer C.range T (1 : ℂ)
  refine ⟨m, hm, ?_, ?_⟩
  · intro z
    have hh := hpair (C z) (LinearMap.mem_range_self C z)
    simpa only [hTC, RCLike.inner_apply', starRingEnd_apply, mul_one] using hh
  · have hn' : ‖m‖ ≤ sqrt W / sqrt c := by
      simpa only [norm_one, mul_one] using hn.trans
        (mul_le_mul_of_nonneg_right hT (norm_nonneg (1 : ℂ)))
    have hs := (sq_le_sq₀ (norm_nonneg m) (by positivity : 0 ≤ sqrt W / sqrt c)).mpr hn'
    rw [div_pow, sq_sqrt hW, sq_sqrt hc.le] at hs
    convert! hs using 1
    dsimp only [W]
    ring

/-- The Christoffel density for a frame orthonormal in the actual
covariance, rather than in a reference Gram. It is the squared norm of the
actual physical score projected onto that frame. -/
theorem finite_heat_covariance_frame_bound (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) →
      ∀ {D G : Type*} [AddCommGroup D] [Module ℂ D]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (S : D →ₗ[ℂ] heatSpan t a) (C : D →ₗ[ℂ] G) [CompleteSpace C.range]
      (c : ℝ), 0 < c → (∀ z, c * ‖S z‖ ^ 2 ≤ ‖C z‖ ^ 2) →
      ∀ (r : ℕ) (z : Fin r → D), Orthonormal ℂ (fun j => C (z j)) →
      ∀ x : UnitAddCircle,
      ∑ j, ‖evaluation t a ht x (S (z j))‖ ^ 2 ≤
        (K / c) * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := finite_heat_covariance_score_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro t a ht hth D G _ _ _ _ _ S C _ c hc hcov r z hz x
  obtain ⟨m, _, hpair, hn⟩ := hscore t a ht hth S C c hc hcov x
  calc
    _ = ∑ j, ‖inner ℂ (C (z j)) m‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hpair, norm_star]
    _ ≤ ‖m‖ ^ 2 := by simpa using hz.sum_inner_products_le m (s := Finset.univ)
    _ ≤ _ := hn

/-- A scaled physical row bound gives the exact squared scale in its
covariance score. The zero-scale case is proved directly, so clipped mass
factors are retained even when they vanish. -/
theorem finite_heat_energy_score_bound (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) →
      ∀ {D G : Type*} [AddCommGroup D] [Module ℂ D]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (S : D →ₗ[ℂ] heatSpan t a) (C : D →ₗ[ℂ] G) [CompleteSpace C.range]
      (energy : D → ℝ) (c L : ℝ), 0 < c → 0 ≤ L →
      (∀ z, ‖S z‖ ^ 2 ≤ L ^ 2 * energy z) →
      (∀ z, c * energy z ≤ ‖C z‖ ^ 2) →
      ∀ x : UnitAddCircle, ∃ m ∈ C.range,
      (∀ z, inner ℂ (C z) m = star (evaluation t a ht x (S z))) ∧
      ‖m‖ ^ 2 ≤ (K * L ^ 2 / c) * ∑ i, SHE.GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := finite_heat_covariance_score_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro t a ht hth D G _ _ _ _ _ S C _ energy c L hc hL hrow hcov x
  by_cases hL0 : L = 0
  · have hS (z : D) : S z = 0 := by
      have h := hrow z
      rw [hL0, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (S z)])
    refine ⟨0, C.range.zero_mem, ?_, ?_⟩
    · intro z
      rw [hS, map_zero, star_zero, inner_zero_right]
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), hL0, mul_zero, zero_mul, zero_div,
        le_refl]
  · have hL2 : 0 < L ^ 2 := sq_pos_of_ne_zero hL0
    have hdom (z : D) : (c / L ^ 2) * ‖S z‖ ^ 2 ≤ ‖C z‖ ^ 2 := by
      calc
        _ ≤ (c / L ^ 2) * (L ^ 2 * energy z) :=
          mul_le_mul_of_nonneg_left (hrow z) (by positivity)
        _ = c * energy z := by field_simp
        _ ≤ _ := hcov z
    obtain ⟨m, hm, hp, hn⟩ := hscore t a ht hth S C (c / L ^ 2) (by positivity) hdom x
    refine ⟨m, hm, hp, ?_⟩
    convert! hn using 1
    congr 1
    field_simp

end SHE.HeatChristoffel
