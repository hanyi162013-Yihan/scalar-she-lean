module

public import SHE.GaussianTaylorAverage
public import SHE.PositiveMatrixBounds
public import SHE.CovarianceContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

/-! Actual Gaussian differentiation along monotone PSD covariance paths.
Singular covariance and colliding observations are retained throughout. -/
noncomputable section
namespace SHE.GaussianCovariancePath
open Set MeasureTheory ProbabilityTheory Filter Asymptotics
open GaussianIncrement GaussianTaylor GaussianTaylorAverage GaussianConvolution GaussianContinuity
open scoped Matrix.Norms.Elementwise

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def actionLinear {n : ℕ} (H : State n →L[ℝ] State n →L[ℝ] ℝ) : Mat n →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun A => covarianceAction A H
        map_add' := by
          intro A B
          simp only [covarianceAction, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro r A
          simp only [covarianceAction, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply] }
    cont := by
      change Continuous (fun A : Mat n => ∑ i : Fin n, ∑ j : Fin n,
        A i j * H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
      fun_prop }

@[simp] theorem actionLinear_apply {n : ℕ} (H : State n →L[ℝ] State n →L[ℝ] ℝ) (A : Mat n) :
    actionLinear H A = covarianceAction A H := rfl

theorem action_sub_left {n : ℕ} (A B : Mat n) (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    covarianceAction (A - B) H = covarianceAction A H - covarianceAction B H := map_sub (actionLinear H) A B

theorem action_sub_right {n : ℕ} (A : Mat n) (H K : State n →L[ℝ] State n →L[ℝ] ℝ) :
    covarianceAction A (H - K) = covarianceAction A H - covarianceAction A K := by
  simp only [covarianceAction, sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ordered_covariance_lipschitz {n : ℕ} {A C : Mat n}
    (hA : A.PosSemidef) (hC : C.PosSemidef)
    (horder : (A - C).PosSemidef ∨ (C - A).PosSemidef)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (z : State n) :
    ‖gaussianAverage A F z - gaussianAverage C F z‖ ≤ B * |A.trace - C.trace| := by
  rcases horder with hAC | hCA
  · have ht : 0 ≤ A.trace - C.trace := by simpa only [Matrix.trace_sub] using hAC.trace_nonneg
    have he := gaussian_covariance_quadratic_bound hAC hC hF hbound hD hDD hB z
    rw [show C + (A - C) = A by abel, Matrix.trace_sub, ← abs_of_nonneg ht] at he
    exact he
  · have ht : 0 ≤ C.trace - A.trace := by simpa only [Matrix.trace_sub] using hCA.trace_nonneg
    have he := gaussian_covariance_quadratic_bound hCA hA hF hbound hD hDD hB z
    rw [show A + (C - A) = C by abel, Matrix.trace_sub] at he
    rw [norm_sub_rev, abs_of_nonpos (by linarith : A.trace - C.trace ≤ 0), neg_sub]
    exact he

/-- Taylor expansion for either order of two actual PSD covariances. The
reference Hessian is always taken at the specified background `C`. -/
theorem ordered_covariance_taylor {n : ℕ} {A C : Mat n}
    (hA : A.PosSemidef) (hC : C.PosSemidef)
    (horder : (A - C).PosSemidef ∨ (C - A).PosSemidef)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L D K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ D) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : State n) :
    ‖gaussianAverage A F z - gaussianAverage C F z - (1 / 2 : ℝ) *
        covarianceAction (A - C) (hessian (gaussianAverage C F) z)‖ ≤
      |A.trace - C.trace| * (K * Real.sqrt (3 * n) * Real.sqrt |A.trace - C.trace| +
        (1 / 2 : ℝ) * (n : ℝ) ^ 2 *
          ‖hessian (gaussianAverage A F) z - hessian (gaussianAverage C F) z‖) := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  rcases horder with hAC | hCA
  · have ht : 0 ≤ A.trace - C.trace := by simpa only [Matrix.trace_sub] using hAC.trace_nonneg
    have he := gaussian_covariance_increment hAC hC hF hbound hD hDD hK hH z
    rw [show C + (A - C) = A by abel, Matrix.trace_sub] at he
    rw [abs_of_nonneg ht]
    calc
      _ ≤ K * (Real.sqrt (3 * n) * (A.trace - C.trace) * Real.sqrt (A.trace - C.trace)) := he
      _ = (A.trace - C.trace) * (K * Real.sqrt (3 * n) * Real.sqrt (A.trace - C.trace)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) ht
  · have ht : 0 ≤ C.trace - A.trace := by simpa only [Matrix.trace_sub] using hCA.trace_nonneg
    have he := gaussian_covariance_increment hCA hA hF hbound hD hDD hK hH z
    rw [show A + (C - A) = C by abel, Matrix.trace_sub] at he
    have hneg : covarianceAction (A - C) (hessian (gaussianAverage C F) z) =
        -covarianceAction (C - A) (hessian (gaussianAverage C F) z) := by
      rw [action_sub_left, action_sub_left]
      ring
    have hb := PositiveMatrixBounds.covariance_action_bound (C - A) hCA
      (hessian (gaussianAverage C F) z - hessian (gaussianAverage A F) z)
    change ‖covarianceAction (C - A) (hessian (gaussianAverage C F) z - hessian (gaussianAverage A F) z)‖ ≤ _ at hb
    rw [Matrix.trace_sub] at hb
    have hsym : ‖hessian (gaussianAverage C F) z - hessian (gaussianAverage A F) z‖ =
        ‖hessian (gaussianAverage A F) z - hessian (gaussianAverage C F) z‖ := norm_sub_rev _ _
    rw [hsym] at hb
    rw [abs_of_nonpos (by linarith : A.trace - C.trace ≤ 0), neg_sub]
    calc
      _ = ‖-(gaussianAverage C F z - gaussianAverage A F z - (1 / 2 : ℝ) *
          covarianceAction (C - A) (hessian (gaussianAverage A F) z)) + (1 / 2 : ℝ) *
          covarianceAction (C - A) (hessian (gaussianAverage C F) z - hessian (gaussianAverage A F) z)‖ := by
        congr 1
        rw [hneg, action_sub_right]
        ring
      _ ≤ ‖gaussianAverage C F z - gaussianAverage A F z - (1 / 2 : ℝ) *
          covarianceAction (C - A) (hessian (gaussianAverage A F) z)‖ + (1 / 2 : ℝ) *
          ‖covarianceAction (C - A) (hessian (gaussianAverage C F) z - hessian (gaussianAverage A F) z)‖ := by
        have hh := norm_add_le
          (-(gaussianAverage C F z - gaussianAverage A F z - (1 / 2 : ℝ) * covarianceAction (C - A) (hessian (gaussianAverage A F) z)))
          ((1 / 2 : ℝ) * covarianceAction (C - A) (hessian (gaussianAverage C F) z - hessian (gaussianAverage A F) z))
        simpa only [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hh
      _ ≤ K * (Real.sqrt (3 * n) * (C.trace - A.trace) * Real.sqrt (C.trace - A.trace)) +
          (1 / 2 : ℝ) * ((n : ℝ) ^ 2 * (C.trace - A.trace) *
            ‖hessian (gaussianAverage A F) z - hessian (gaussianAverage C F) z‖) :=
        add_le_add he (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = _ := by ring

/-- The deterministic Gaussian backward equation along an actual decreasing
PSD covariance path. Only differentiability of that covariance path is a
premise; the Gaussian differentiation and singular-rank passage are proved. -/
theorem hasDerivAt_monotone_gaussian_average {n : ℕ}
    (C : ℝ → PositiveCovariance n) {D : Mat n} {q : ℝ}
    (hC : HasDerivAt (fun t => (C t).val) D q)
    (horder : ∀ u v, u ≤ v → ((C u).val - (C v).val).PosSemidef)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : State n) :
    HasDerivAt (fun t => gaussianAverage (C t).val F z)
      ((1 / 2 : ℝ) * covarianceAction D (hessian (gaussianAverage (C q).val F) z)) q := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  let f : ℝ → ℝ := fun t => gaussianAverage (C t).val F z
  let G : ℝ → State n →L[ℝ] State n →L[ℝ] ℝ := fun t => hessian (gaussianAverage (C t).val F) z
  let a : ℝ → ℝ := fun t => |(C t).val.trace - (C q).val.trace|
  let b : ℝ → ℝ := fun t => K * Real.sqrt (3 * n) * Real.sqrt (a t) + (1 / 2 : ℝ) * (n : ℝ) ^ 2 * ‖G t - G q‖
  let R : ℝ → ℝ := fun t => f t - f q - (1 / 2 : ℝ) * covarianceAction ((C t).val - (C q).val) (G q)
  have hentry (i j : Fin n) : HasDerivAt (fun t => (C t).val i j) (D i j) q := by
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hC i) j
  have htr : HasDerivAt (fun t => (C t).val.trace) D.trace q := by
    simpa only [Matrix.trace, Matrix.diag] using HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hentry i i)
  have haO : a =O[nhds q] (fun t => t - q) := by
    simpa only [a, Real.norm_eq_abs] using htr.isBigO_sub.norm_left
  have ha : Tendsto a (nhds q) (nhds 0) := by
    simpa only [a, sub_self, Real.norm_eq_abs, norm_zero] using
      (htr.continuousAt.tendsto.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => (C q).val.trace) (nhds q) _)).norm
  have hG : ContinuousAt G q := by
    have hHC : Continuous (hessian F) := (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
    have hPC : ContinuousAt C q := tendsto_subtype_rng.mpr hC.continuousAt
    have hp : ContinuousAt (fun t => (C t, z)) q := hPC.prodMk continuousAt_const
    have hg := (continuous_gaussian_average (n := n) (hessian F) hHC hDD).continuousAt.comp hp
    have heq : G = fun t => ∫ y : State n, hessian F (z + y) ∂multivariateGaussian 0 (C t).val := by
      funext t
      dsimp only [G, hessian]
      rw [show gaussianAverage (C t).val F = GaussianSmooth.average (multivariateGaussian 0 (C t).val) F from rfl,
        GaussianSmooth.fderiv_fderiv_average _ hF hbound hD hDD]
      rfl
    rw [heq]
    exact hg
  have hb : Tendsto b (nhds q) (nhds 0) := by
    have hs := ha.sqrt
    have hg := (hG.tendsto.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => G q) (nhds q) _)).norm
    have hh := (hs.const_mul (K * Real.sqrt (3 * n))).add (hg.const_mul ((1 / 2 : ℝ) * (n : ℝ) ^ 2))
    simpa only [b, sub_self, norm_zero, Real.sqrt_zero, mul_zero, add_zero] using hh
  have hb0 (t : ℝ) : 0 ≤ b t := by dsimp [b]; positivity
  have hpoint (t : ℝ) : ‖R t‖ ≤ a t * b t := by
    exact ordered_covariance_taylor (C t).property (C q).property
      (by rcases le_total t q with ht | ht
          · exact Or.inl (horder t q ht)
          · exact Or.inr (horder q t ht)) hF hbound hD hDD hK hH z
  have hRO : R =O[nhds q] (fun t => a t * b t) := by
    refine isBigO_iff.mpr ⟨1, Eventually.of_forall (fun t => ?_)⟩
    simpa only [one_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ a t from abs_nonneg _),
      abs_of_nonneg (hb0 t)] using hpoint t
  have hprod : (fun t => a t * b t) =o[nhds q] (fun t => t - q) := by
    simpa only [mul_one] using haO.mul_isLittleO ((isLittleO_one_iff ℝ).mpr hb)
  have hRsmall := hRO.trans_isLittleO hprod
  have hlin := ((actionLinear (G q)).hasFDerivAt.comp_hasDerivAt q hC).const_mul (1 / 2 : ℝ)
  simp only [Function.comp_def, actionLinear_apply] at hlin
  have hh := hRsmall.add hlin.isLittleO
  apply HasDerivAt.of_isLittleO
  convert hh using 1
  funext t
  dsimp [R, f]
  rw [action_sub_left]
  ring

end SHE.GaussianCovariancePath
