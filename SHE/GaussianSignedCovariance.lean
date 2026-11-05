module

public import SHE.GaussianCovariancePath

/-! Signed, nonmonotone covariance comparison and differentiation. Two
nearby PSD covariances have a genuine common upper covariance at distance
O(‖A-C‖); actual ordered Gaussian Taylor estimates can therefore be applied
twice without a covariance-order assumption. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
noncomputable section

namespace SHE.GaussianSignedCovariance
open Set MeasureTheory ProbabilityTheory Filter Asymptotics Matrix
  SHE.GaussianIncrement SHE.GaussianTaylor SHE.GaussianTaylorAverage
  SHE.GaussianConvolution SHE.GaussianContinuity SHE.GaussianCovariancePath
open scoped MatrixOrder Matrix.Norms.L2Operator

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

theorem hermitian_le_norm_scalar {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    A ≤ ‖A‖ • (1 : Mat n) := by
  by_cases hn : n = 0
  · subst n
    exact le_of_eq (Subsingleton.elim _ _)
  have : NeZero n := ⟨hn⟩
  have h := le_algebraMap_of_spectrum_le (R := ℝ) (a := A)
    (fun x hx => (Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx))
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)
  simpa only [Algebra.algebraMap_eq_smul_one] using h

def commonUpper {n : ℕ} (A C : Mat n) : Mat n := C + ‖A - C‖ • (1 : Mat n)

theorem commonUpper_sub_right_positive {n : ℕ} (A C : Mat n) :
    (commonUpper A C - C).PosSemidef := by
  simpa only [commonUpper, add_sub_cancel_left] using
    (Matrix.PosSemidef.one : (1 : Mat n).PosSemidef).smul (norm_nonneg (A - C))

theorem commonUpper_sub_left_positive {n : ℕ} (A C : Mat n)
    (hA : A.IsHermitian) (hC : C.IsHermitian) : (commonUpper A C - A).PosSemidef := by
  have h := hermitian_le_norm_scalar (A - C) (hA.sub hC)
  have hp : (‖A - C‖ • (1 : Mat n) - (A - C)).PosSemidef := Matrix.le_iff.mp h
  convert! hp using 1
  unfold commonUpper
  abel

theorem commonUpper_positive {n : ℕ} (A C : Mat n) (hC : C.PosSemidef) :
    (commonUpper A C).PosSemidef := by
  have hp := hC.add (commonUpper_sub_right_positive A C)
  simpa only [commonUpper, add_sub_cancel_left] using hp

theorem commonUpper_trace_right {n : ℕ} (A C : Mat n) :
    (commonUpper A C).trace - C.trace = (n : ℝ) * ‖A - C‖ := by
  simp only [commonUpper, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, add_sub_cancel_left, mul_comm]

theorem commonUpper_trace_left {n : ℕ} (A C : Mat n) :
    (commonUpper A C).trace - A.trace = (n : ℝ) * ‖A - C‖ - (A.trace - C.trace) := by
  have h := commonUpper_trace_right A C
  linarith

theorem continuous_averaged_hessian {n : ℕ}
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (z : State n) :
    Continuous (fun A : PositiveCovariance n => hessian (gaussianAverage A.val F) z) := by
  have hHF : Continuous (hessian F) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  have hg := (continuous_gaussian_average (n := n) (hessian F) hHF hDD).comp
    (continuous_id.prodMk continuous_const : Continuous (fun A : PositiveCovariance n => (A, z)))
  convert! hg using 1
  funext A
  dsimp only [hessian]
  rw [show gaussianAverage A.val F = GaussianSmooth.average (multivariateGaussian 0 A.val) F from rfl,
    GaussianSmooth.fderiv_fderiv_average _ hF hbound hD hDD]
  rfl

theorem ordered_pair_remainder_bound {n : ℕ} {A C : Mat n}
    (hA : A.PosSemidef) (hC : C.PosSemidef) (hAC : (A - C).PosSemidef)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖)
    (z : State n) (H₀ : State n →L[ℝ] State n →L[ℝ] ℝ) :
    ‖gaussianAverage A F z - gaussianAverage C F z -
        (1 / 2 : ℝ) * covarianceAction (A - C) H₀‖ ≤
      (A.trace - C.trace) * (K * Real.sqrt (3 * n) * Real.sqrt (A.trace - C.trace) +
        (1 / 2 : ℝ) * (n : ℝ) ^ 2 *
        (‖hessian (gaussianAverage A F) z - hessian (gaussianAverage C F) z‖ +
          ‖hessian (gaussianAverage C F) z - H₀‖)) := by
  have ht : 0 ≤ A.trace - C.trace := by simpa only [Matrix.trace_sub] using hAC.trace_nonneg
  have hbase := ordered_covariance_taylor hA hC (Or.inl hAC) hF hbound hD hDD hK hH z
  rw [abs_of_nonneg ht] at hbase
  have hcross := SHE.PositiveMatrixBounds.covariance_action_bound (A - C) hAC
    (hessian (gaussianAverage C F) z - H₀)
  change ‖covarianceAction (A - C) (hessian (gaussianAverage C F) z - H₀)‖ ≤ _ at hcross
  rw [Matrix.trace_sub] at hcross
  calc
    _ = ‖(gaussianAverage A F z - gaussianAverage C F z - (1 / 2 : ℝ) *
          covarianceAction (A - C) (hessian (gaussianAverage C F) z)) +
        (1 / 2 : ℝ) * covarianceAction (A - C) (hessian (gaussianAverage C F) z - H₀)‖ := by
      congr 1
      rw [action_sub_right]
      ring
    _ ≤ ‖gaussianAverage A F z - gaussianAverage C F z - (1 / 2 : ℝ) *
          covarianceAction (A - C) (hessian (gaussianAverage C F) z)‖ +
        (1 / 2 : ℝ) * ‖covarianceAction (A - C) (hessian (gaussianAverage C F) z - H₀)‖ := by
      have hh := norm_add_le
        (gaussianAverage A F z - gaussianAverage C F z - (1 / 2 : ℝ) *
          covarianceAction (A - C) (hessian (gaussianAverage C F) z))
        ((1 / 2 : ℝ) * covarianceAction (A - C) (hessian (gaussianAverage C F) z - H₀))
      simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hh
    _ ≤ (A.trace - C.trace) * (K * Real.sqrt (3 * n) * Real.sqrt (A.trace - C.trace) +
          (1 / 2 : ℝ) * (n : ℝ) ^ 2 *
            ‖hessian (gaussianAverage A F) z - hessian (gaussianAverage C F) z‖) +
        (1 / 2 : ℝ) * ((n : ℝ) ^ 2 * (A.trace - C.trace) *
          ‖hessian (gaussianAverage C F) z - H₀‖) :=
      add_le_add hbase (mul_le_mul_of_nonneg_left hcross (by norm_num))
    _ = _ := by ring

/-- An ordered pair of PSD paths has a first covariance expansion around
their common limiting Hessian. Only the trace increment is required to be
O(t-q); neither path needs to be monotone or differentiable separately. -/
theorem ordered_paths_remainder_isLittleO {n : ℕ}
    (A C : ℝ → PositiveCovariance n) {q : ℝ}
    (hA : ContinuousAt A q) (hC : ContinuousAt C q) (heq : A q = C q)
    (horder : ∀ t, ((A t).val - (C t).val).PosSemidef)
    (htrace : (fun t => (A t).val.trace - (C t).val.trace) =O[nhds q] (fun t => t - q))
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : State n) :
    (fun t => gaussianAverage (A t).val F z - gaussianAverage (C t).val F z -
      (1 / 2 : ℝ) * covarianceAction ((A t).val - (C t).val)
        (hessian (gaussianAverage (C q).val F) z)) =o[nhds q] (fun t => t - q) := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  let H : PositiveCovariance n → State n →L[ℝ] State n →L[ℝ] ℝ :=
    fun V => hessian (gaussianAverage V.val F) z
  let a : ℝ → ℝ := fun t => (A t).val.trace - (C t).val.trace
  let b : ℝ → ℝ := fun t => K * Real.sqrt (3 * n) * Real.sqrt (a t) +
    (1 / 2 : ℝ) * (n : ℝ) ^ 2 * (‖H (A t) - H (C t)‖ + ‖H (C t) - H (C q)‖)
  let R : ℝ → ℝ := fun t => gaussianAverage (A t).val F z - gaussianAverage (C t).val F z -
    (1 / 2 : ℝ) * covarianceAction ((A t).val - (C t).val) (H (C q))
  have ha0 (t : ℝ) : 0 ≤ a t := by
    simpa only [a, Matrix.trace_sub] using (horder t).trace_nonneg
  have ha : Tendsto a (nhds q) (nhds 0) := by
    have hAv : ContinuousAt (fun t => (A t).val) q := continuous_subtype_val.continuousAt.comp hA
    have hCv : ContinuousAt (fun t => (C t).val) q := continuous_subtype_val.continuousAt.comp hC
    have hh := ((continuous_id.matrix_trace.continuousAt.comp hAv).sub
      (continuous_id.matrix_trace.continuousAt.comp hCv)).tendsto
    convert! hh using 1; simp only [Function.comp_def, id_eq, Pi.sub_apply, heq, sub_self]
  have hHc : Continuous H := continuous_averaged_hessian hF hbound hD hDD z
  have hHA := hHc.continuousAt.comp hA
  have hHC := hHc.continuousAt.comp hC
  have hab : Tendsto (fun t => ‖H (A t) - H (C t)‖) (nhds q) (nhds 0) := by
    convert! (hHA.tendsto.sub hHC.tendsto).norm using 1;
      simp only [Function.comp_def, heq, sub_self, norm_zero]
  have hbc : Tendsto (fun t => ‖H (C t) - H (C q)‖) (nhds q) (nhds 0) := by
    have hh := (hHC.tendsto.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => H (C q)) (nhds q) (nhds (H (C q))))).norm
    convert! hh using 1; simp only [Function.comp_def, sub_self, norm_zero]
  have hb : Tendsto b (nhds q) (nhds 0) := by
    have hh := ((ha.sqrt).const_mul (K * Real.sqrt (3 * n))).add
      ((hab.add hbc).const_mul ((1 / 2 : ℝ) * (n : ℝ) ^ 2))
    simpa only [b, Real.sqrt_zero, mul_zero, add_zero] using hh
  have hb0 (t : ℝ) : 0 ≤ b t := by dsimp only [b]; positivity
  have hpoint (t : ℝ) : ‖R t‖ ≤ a t * b t :=
    ordered_pair_remainder_bound (A t).property (C t).property (horder t)
      hF hbound hD hDD hK hH z (H (C q))
  have hRO : R =O[nhds q] (fun t => a t * b t) := by
    refine isBigO_iff.mpr ⟨1, Eventually.of_forall (fun t => ?_)⟩
    simpa only [one_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (ha0 t),
      abs_of_nonneg (hb0 t)] using hpoint t
  have hprod : (fun t => a t * b t) =o[nhds q] (fun t => t - q) := by
    simpa only [mul_one] using htrace.mul_isLittleO ((isLittleO_one_iff ℝ).mpr hb)
  exact hRO.trans_isLittleO hprod

/-- Genuine Gaussian differentiation along every differentiable PSD
covariance path, with no monotonicity, strict positivity or fixed-rank
hypothesis. In particular the covariance direction may be signed. -/
theorem hasDerivAt_gaussian_average {n : ℕ}
    (C : ℝ → PositiveCovariance n) {D : Mat n} {q : ℝ}
    (hC : HasDerivAt (fun t => (C t).val) D q)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w, ‖hessian F w - hessian F z‖ ≤ K * ‖w - z‖) (z : State n) :
    HasDerivAt (fun t => gaussianAverage (C t).val F z)
      ((1 / 2 : ℝ) * covarianceAction D (hessian (gaussianAverage (C q).val F) z)) q := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  let U : ℝ → PositiveCovariance n := fun t =>
    ⟨commonUpper (C t).val (C q).val, commonUpper_positive _ _ (C q).property⟩
  have hCc : ContinuousAt C q := tendsto_subtype_rng.mpr hC.continuousAt
  have hUc : ContinuousAt U q := by
    apply tendsto_subtype_rng.mpr
    change ContinuousAt (fun t => (C q).val + ‖(C t).val - (C q).val‖ • (1 : Mat n)) q
    exact continuousAt_const.add ((hC.continuousAt.sub continuousAt_const).norm.smul continuousAt_const)
  have hUq : U q = C q := by
    apply Subtype.ext
    simp only [U, commonUpper, sub_self, norm_zero, zero_smul, add_zero]
  let tr : Mat n →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap
  have htr : HasDerivAt (fun t => (C t).val.trace) D.trace q := by
    exact tr.hasFDerivAt.comp_hasDerivAt q hC
  have hright : (fun t => (U t).val.trace - (C q).val.trace) =O[nhds q] (fun t => t - q) := by
    have hh := hC.isBigO_sub.norm_left.const_mul_left (n : ℝ)
    convert! hh using 1
    funext t
    exact commonUpper_trace_right (C t).val (C q).val
  have hleft : (fun t => (U t).val.trace - (C t).val.trace) =O[nhds q] (fun t => t - q) := by
    have hh := hright.sub htr.isBigO_sub
    convert! hh using 1
    funext t
    ring
  have hR₁ := ordered_paths_remainder_isLittleO U (fun _ => C q) hUc continuousAt_const hUq
    (fun t => commonUpper_sub_right_positive (C t).val (C q).val) hright
    hF hbound hD hDD hK hH z
  have hR₂ := ordered_paths_remainder_isLittleO U C hUc hCc hUq
    (fun t => commonUpper_sub_left_positive (C t).val (C q).val
      (C t).property.isHermitian (C q).property.isHermitian) hleft
    hF hbound hD hDD hK hH z
  have hrem : (fun t => gaussianAverage (C t).val F z - gaussianAverage (C q).val F z -
      (1 / 2 : ℝ) * covarianceAction ((C t).val - (C q).val)
        (hessian (gaussianAverage (C q).val F) z)) =o[nhds q] (fun t => t - q) := by
    have hh := hR₁.sub hR₂
    convert! hh using 1
    funext t
    simp only [action_sub_left]
    ring
  let H₀ := hessian (gaussianAverage (C q).val F) z
  let T : Mat n →L[ℝ] ℝ := (actionLinear H₀).toLinearMap.toContinuousLinearMap
  have hT (A : Mat n) : T A = covarianceAction A H₀ := rfl
  have hlin := (T.hasFDerivAt.comp_hasDerivAt q hC).const_mul (1 / 2 : ℝ)
  have hh := hrem.add hlin.isLittleO
  apply HasDerivAt.of_isLittleO
  convert! hh using 1
  funext t
  change gaussianAverage (C t).val F z - gaussianAverage (C q).val F z -
    (t - q) * ((1 / 2 : ℝ) * covarianceAction D H₀) = _
  simp only [Function.comp_def, hT, action_sub_left, smul_eq_mul]
  dsimp only [H₀]
  ring

end SHE.GaussianSignedCovariance
