module

public import SHE.GaussianFirstSplit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GaussianFullResidualScore
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  SmoothCylinders MeasurableGaussianScores
variable {n : ℕ}

/-- The entire remaining Gaussian can carry the fresh first score.
No smaller front-interval range condition is needed. An exact existing
representation keeps every old score inside the same bounded test. -/
theorem fderiv_eq_firstScore
    {C T : MeasurableGeneralizedInverse.Mat n} (hT : T.PosSemidef)
    {d : State n} (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) T).range)
    {F G : State n → ℝ} (hF : BoundedSmooth F) (hG : Measurable G)
    (M : ℝ) (hGb : ∀ w,|G w|≤M)
    (hrep : gaussianAverage C F=gaussianAverage T G) (z : State n) :
    fderiv ℝ (gaussianAverage C F) z d=
      ∫ y,G (z+y)*firstScore T d y ∂multivariateGaussian 0 T := by
  have hh := GaussianMeanScores.hasDerivAt_physical_mean hT hd
    (fun y => G (z+y)) (hG.comp (measurable_const.add measurable_id)) M (fun _ => hGb _) 0
  have he : (fun s : ℝ => ∫ y,G (z+(y+s•d)) ∂multivariateGaussian 0 T)=
      fun s => gaussianAverage C F (z+s•d) := by
    funext s
    rw [hrep]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by congr 1;abel)
  rw [he] at hh
  have hH : BoundedSmooth (gaussianAverage C F) :=
    hF.average (multivariateGaussian (0 : State n) C)
  have hline : HasDerivAt (fun s : ℝ => z+s•d) d 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add z using 1 <;>
      simp only [id_eq,one_smul]
  have hg := (hH.smooth.differentiable (by simp) (z+(0:ℝ)•d)).hasFDerivAt.comp_hasDerivAt 0 hline
  simpa only [zero_smul,add_zero,Function.comp_def] using hg.unique hh

end SHE.GaussianFullResidualScore
