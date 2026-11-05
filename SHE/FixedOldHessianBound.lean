module

public import SHE.GaussianFullResidualScore
public import SHE.GaussianFixedScore
public import SHE.BoundedOldAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.FixedOldHessianBound
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
open SmoothCylinders MeasurableGaussianScores GaussianHessianScore
variable {n : ℕ}

/-- The entire remaining law carries the TRUE second derivative while
all old fixed scores remain inside G. The bound below therefore never
uses derivatives of a coefficient approximation. -/
theorem hessian_eq_secondScore {C T : MeasurableGeneralizedInverse.Mat n}
    (hT : T.PosSemidef) {d : State n}
    (hd : d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range)
    {F G : State n→ℝ} (hF : BoundedSmooth F) (hG : Measurable G)
    (M : ℝ) (hGb : ∀w,|G w|≤M)
    (hrep : gaussianAverage C F=gaussianAverage T G) (z : State n) :
    WordRecursion.directionalSecond (gaussianAverage C F) z d=
      ∫y,G (z+y)*secondScore T d y ∂multivariateGaussian 0 T := by
  have hh:=GaussianMeanScores.hasDerivAt_deriv_physical_mean hT hd
    (fun y=>G (z+y)) (hG.comp (measurable_const.add measurable_id)) M (fun _=>hGb _) 0
  have he:(fun s:ℝ=>∫y,G (z+(y+s•d)) ∂multivariateGaussian 0 T)=
      fun s=>gaussianAverage C F (z+s•d):=by
    funext s
    rw [hrep]
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>by congr 1;abel)
  rw [he] at hh
  obtain ⟨B,hB⟩:=hF.norm_bound
  obtain ⟨L,hL⟩:=hF.fderiv.norm_bound
  obtain ⟨K,hK⟩:=hF.fderiv.fderiv.norm_bound
  have hg:=hasDerivAt_deriv_average_affine_line (multivariateGaussian (0:State n) C)
    (hF.smooth.of_le (by simp)) hB hL hK z d
  simp only [zero_smul,add_zero] at hh
  exact hg.unique hh

theorem hessian_bound {C T : MeasurableGeneralizedInverse.Mat n}
    (hT : T.PosSemidef) {d : State n}
    (hd : d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range)
    {F G : State n→ℝ} (hF : BoundedSmooth F) (hG : Measurable G)
    (M : ℝ) (hM : 0≤M) (hGb : ∀w,|G w|≤M)
    (hrep : gaussianAverage C F=gaussianAverage T G) (z : State n) :
    |WordRecursion.directionalSecond (gaussianAverage C F) z d|≤2*M*scoreVariance T d := by
  rw [hessian_eq_secondScore hT hd hF hG M hGb hrep]
  have hb:=centered_square_score_integral_bound (multivariateGaussian (0:State n) T)
    (innerSL ℝ (coefficient T d)) (firstScore_mean_zero T d)
      (fun y=>G (z+y)) M hM (fun y=>hGb _)
  rw [firstScore_variance hT hd] at hb
  exact hb

end SHE.FixedOldHessianBound

namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers GaussianCoordinates PhysicalScoreChain SmoothCylinders GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance fixedOldHessianBound_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n N : ℕ}
variable (L : Level R X n)

def oldAbsoluteMass (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (p : History X k) : ℝ :=
  ∫x:Fin k→WordRecursion.State (n+k),|∏j,secondScore
    (covariances L ((carrier L k).observations.observations p) c k p j)
    (directions L ((carrier L k).observations.observations p) k p j) (x j)|
    ∂Measure.pi (fun j=>multivariateGaussian 0
      (covariances L ((carrier L k).observations.observations p) c k p j))

theorem oldAbsoluteMass_nonneg (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (p : History X k) :
    0≤oldAbsoluteMass L c k p:=integral_nonneg (fun _=>abs_nonneg _)

/-- A cap for the literal root times every centered physical leaf.
Only zeroth-order coefficient caps occur. -/
theorem word_cap {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (ha : ∀z,|R.totalVariance z|≤A) (hroot : ∀p z,|L.test p z|≤B)
    (k : ℕ) (p : History X k) (g : Fin (n+k)→Fin N) (z : WordRecursion.State N) :
    |word L k p g z|≤B*((A+R.upper)/2)^k := by
  have hleaf (j:Fin k):|leaves L k p g j z|≤(A+R.upper)/2:=by
    simp only [leaves,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh:|R.totalVariance (z (leafIndex k g j))-baseline L k p j|≤A+R.upper:=
      (abs_sub _ _).trans (add_le_add (ha _) (R.reference_bound _))
    nlinarith
  rw [word,abs_mul,Finset.abs_prod]
  have hp:(∏j:Fin k,|leaves L k p g j z|)≤((A+R.upper)/2)^k:=by
    calc
      _≤∏_j:Fin k,(A+R.upper)/2:=Finset.prod_le_prod₀ (fun _ _=>abs_nonneg _) (fun j _=>hleaf j)
      _=_:=by rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul (hroot _ _) hp (Finset.prod_nonneg (fun _ _=>abs_nonneg _)) hB

/-- The state cap of the actual old average is independent of every
derivative of the approximating coefficient. With a constant fixed old
reserve its remaining geometric weight is independent of that index. -/
theorem oldAverage_cap (c : StoppedGaussianFeatures.Domain→ℝ) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀z,|R.totalVariance z|≤A)
    (hroot : ∀p z,|L.test p z|≤B) (k : ℕ) (p : History X k) (z : WordRecursion.State (n+k)) :
    |oldAverage L c k p z|≤(B*((A+R.upper)/2)^k)*oldAbsoluteMass L c k p := by
  let Z:=(carrier L k).observations.observations p
  let ν:=Measure.pi (fun j:Fin k=>multivariateGaussian (0:WordRecursion.State (n+k)) (covariances L Z c k p j))
  let w:=fun x:Fin k→WordRecursion.State (n+k)=>∏j,secondScore (covariances L Z c k p j) (directions L Z k p j) (x j)
  let shift:=fun x:Fin k→WordRecursion.State (n+k)=>∑j,x j
  have hw:Integrable w ν:=old_weight_integrable L c k p
  have hs:Measurable shift:=Finset.measurable_sum Finset.univ (fun j _=>measurable_pi_apply j)
  have hm:Measurable (word L k p (fun i=>i)):=(word_boundedSmooth L k p _).smooth.continuous.measurable
  have hb:∀y,|word L k p (fun i=>i) y|≤B*((A+R.upper)/2)^k:=word_cap L hA hB ha hroot k p _
  have hp:0≤B*((A+R.upper)/2)^k:=mul_nonneg hB
    (pow_nonneg (div_nonneg (add_nonneg hA R.upper_nonneg) (by norm_num)) _)
  exact WeightedBorelAverage.bound ν w hw shift hs _ hm _ hp hb z

end SHE.PhysicalChainArrays
