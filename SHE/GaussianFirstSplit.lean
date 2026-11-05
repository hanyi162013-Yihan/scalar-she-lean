module

public import SHE.GaussianFixedScore
public import SHE.WeightedBorelAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianFirstSplit
open Set Filter MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  SmoothCylinders MeasurableGaussianScores
variable {n : ℕ}

theorem gaussianAverage_measurable (A : MeasurableGeneralizedInverse.Mat n)
    {F : State n → ℝ} (hF : Measurable F) : Measurable (gaussianAverage A F) := by
  exact (hF.comp (measurable_fst.add measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem gaussianAverage_bound (A : MeasurableGeneralizedInverse.Mat n)
    {F : State n → ℝ} {M : ℝ} (hb : ∀ z, |F z| ≤ M) (z : State n) :
    |gaussianAverage A F z| ≤ M := by
  simpa only [Real.norm_eq_abs,GaussianSmooth.average,gaussianAverage] using
    GaussianSmooth.average_norm_bound (F:=F) (M:=M) (multivariateGaussian (0 : State n) A)
      (fun z => by simpa only [Real.norm_eq_abs] using hb z) z

/-- A genuine first derivative of a bounded Borel Gaussian average puts
its score on the chosen fixed old covariance. The whole residual law
and the original mean remain inside the test. -/
theorem hasDerivAt_split {R B : MeasurableGeneralizedInverse.Mat n}
    (hR : R.PosSemidef) (hB : B.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    {F : State n → ℝ} (hF : Measurable F) (M : ℝ) (hb : ∀ z, |F z| ≤ M)
    (z : State n) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => gaussianAverage (R+B) F (z+s•d))
      (∫ old, ∫ residual, F (z+θ•d+old+residual)*firstScore R d old
        ∂multivariateGaussian 0 B ∂multivariateGaussian 0 R) θ := by
  let G := gaussianAverage B F
  have hG : Measurable G := gaussianAverage_measurable B hF
  have hGb : ∀ w, |G w| ≤ M := gaussianAverage_bound B hb
  have hh := GaussianMeanScores.hasDerivAt_physical_mean hR hd
    (fun y => G (z+y)) (hG.comp (measurable_const.add measurable_id)) M (fun y => hGb _) θ
  have he : (fun s : ℝ => ∫ y, G (z+(y+s•d)) ∂multivariateGaussian 0 R)=
      fun s => gaussianAverage (R+B) F (z+s•d) := by
    funext s
    rw [← gaussianAverage_composition R B hR hB F hF hb]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by
      change G (z+(y+s•d))=G (z+s•d+y)
      congr 1
      abel)
  rw [he] at hh
  convert! hh using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun old => by
    change (∫ residual, F (z+θ•d+old+residual)*firstScore R d old ∂multivariateGaussian 0 B)=
      (∫ residual, F (z+(old+θ•d)+residual) ∂multivariateGaussian 0 B)*firstScore R d old
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun residual => by congr 2; abel))

/-- The actual Fréchet derivative of a bounded smooth cylinder has this
same fixed-old first-score representation, including singular covariance. -/
theorem fderiv_split {R B : MeasurableGeneralizedInverse.Mat n}
    (hR : R.PosSemidef) (hB : B.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    {F : State n → ℝ} (hF : BoundedSmooth F) (z : State n) :
    fderiv ℝ (gaussianAverage (R+B) F) z d =
      ∫ old, ∫ residual, F (z+old+residual)*firstScore R d old
        ∂multivariateGaussian 0 B ∂multivariateGaussian 0 R := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  have hh := hasDerivAt_split hR hB hd hF.smooth.continuous.measurable M
    (fun w => by simpa only [Real.norm_eq_abs] using hM w) z 0
  have hG : BoundedSmooth (gaussianAverage (R+B) F) :=
    hF.average (multivariateGaussian (0 : State n) (R+B))
  have hline : HasDerivAt (fun s : ℝ => z+s•d) d 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add z using 1 <;> simp only [id_eq,one_smul]
  have hg := (hG.smooth.differentiable (by simp) (z+(0:ℝ)•d)).hasFDerivAt.comp_hasDerivAt 0 hline
  simpa only [zero_smul,add_zero,Function.comp_def] using hg.unique hh

/-- Any previously proved reserved-covariance representation is retained
under a true terminal derivative. Only the new terminal old covariance
carries the first score; every earlier fixed old score stays in `G`. -/
theorem fderiv_reserved {R B C : MeasurableGeneralizedInverse.Mat n}
    (hR : R.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    {F G : State n → ℝ} (hF : BoundedSmooth F) (hG : Measurable G)
    (M : ℝ) (hb : ∀ z, |G z| ≤ M) (hrep : F=gaussianAverage C G) (z : State n) :
    fderiv ℝ (gaussianAverage (R+B) F) z d =
      ∫ old, ∫ residual, G (z+old+residual)*firstScore R d old
        ∂multivariateGaussian 0 (B+C) ∂multivariateGaussian 0 R := by
  have he : gaussianAverage (R+B) F=gaussianAverage (R+(B+C)) G := by
    rw [hrep]
    funext w
    rw [gaussianAverage_composition (R+B) C (hR.add hB) hC G hG hb]
    rw [add_assoc]
  have hh := hasDerivAt_split hR (hB.add hC) hd hG M hb z 0
  rw [← he] at hh
  have hH : BoundedSmooth (gaussianAverage (R+B) F) :=
    hF.average (multivariateGaussian (0 : State n) (R+B))
  have hline : HasDerivAt (fun s : ℝ => z+s•d) d 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add z using 1 <;> simp only [one_smul]
  have hg := (hH.smooth.differentiable (by simp) (z+(0:ℝ)•d)).hasFDerivAt.comp_hasDerivAt 0 hline
  simpa only [zero_smul,add_zero,Function.comp_def] using hg.unique hh

/-- Every previously fixed old score stays inside the unchanged weight.
This applies to the full root times all centered leaves, without any
smoothness requirement on those bounded Borel tests. -/
theorem weighted_hasDerivAt_split {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w μ)
    (shift : X → State n) (hs : Measurable shift)
    {R B : MeasurableGeneralizedInverse.Mat n} (hR : R.PosSemidef) (hB : B.PosSemidef)
    {d : State n} (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    {F : State n → ℝ} (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z, |F z| ≤ M)
    (z : State n) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => gaussianAverage (R+B) (WeightedBorelAverage.average μ w shift F) (z+s•d))
      (∫ old, ∫ residual, ∫ x, w x*F (z+θ•d+old+residual+shift x)*firstScore R d old
        ∂μ ∂multivariateGaussian 0 B ∂multivariateGaussian 0 R) θ := by
  have hh := hasDerivAt_split hR hB hd
    (WeightedBorelAverage.measurable μ w hw shift hs F hF)
    (M*∫ x, |w x| ∂μ) (WeightedBorelAverage.bound μ w hwi shift hs F hF M hM hb) z θ
  convert! hh using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun old => by
    apply integral_congr_ae
    exact ae_of_all _ (fun residual => by
      change (∫ x, w x*F (z+θ•d+old+residual+shift x)*firstScore R d old ∂μ)=
        (∫ x, w x*F (z+θ•d+old+residual+shift x) ∂μ)*firstScore R d old
      exact integral_mul_const _ _))

end SHE.GaussianFirstSplit
