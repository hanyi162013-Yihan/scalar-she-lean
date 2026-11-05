module

public import SHE.GaussianMeanScores
public import SHE.ProfileL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The complete bounded Gaussian root/rough covariance word, including its
explicit deterministic baseline, under actual physical mean differentiation. -/
namespace SHE.GaussianCovarianceWord
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAudit GaussianGramScore
  MeasurableGeneralizedInverse MeasurableGaussianScores GaussianMeanScores ProfileL2 Real
open scoped InnerProductSpace
variable {n:ℕ}

def average (A:Mat n) (f:State n→ℝ) (m:State n):ℝ:=∫y,f (m+y) ∂multivariateGaussian 0 A

def word (A:Mat n) (b a:State n→ℝ) (m:State n):ℝ:=
  average A (fun y=>b y*a y) m-average A b m*average A a m

def centeredTest (A:Mat n) (b a:State n→ℝ) (m:State n) (y:State n):ℝ:=
  (b (m+y)-average A b m)*(a (m+y)-average A a m)

theorem average_bound (A:Mat n) (f:State n→ℝ) (M:ℝ) (hM:∀y,|f y|≤M) (m:State n):
    |average A f m|≤M:=by
  have h:=norm_integral_le_of_norm_le_const (μ:=multivariateGaussian (0:State n) A)
    (f:=fun y=>f (m+y)) (C:=M) (ae_of_all _ (fun y=>by simpa only[Real.norm_eq_abs] using hM (m+y)))
  simpa only[average,Real.norm_eq_abs,probReal_univ,mul_one] using h

theorem hasDerivAt_average {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (f:State n→ℝ) (hf:Measurable f) (M:ℝ) (hM:∀y,|f y|≤M) (m:State n) (θ:ℝ):
    HasDerivAt (fun s:ℝ=>average A f (m+s•D))
      (∫y,f (m+θ•D+y)*firstScore A D y ∂multivariateGaussian 0 A) θ:=by
  have h:=hasDerivAt_physical_mean hA hD (fun y=>f (m+y)) (by fun_prop) M (fun y=>hM _) θ
  convert! h using 1
  · funext s
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>by simp only [add_comm,add_left_comm])
  · apply integral_congr_ae
    exact ae_of_all _ (fun y=>by simp only [add_comm,add_left_comm])

private theorem integrable_score_bdd (A:Mat n) (D:State n) (f:State n→ℝ)
    (hf:Measurable f) (M:ℝ) (hM:∀y,|f y|≤M):
    Integrable (fun y=>f y*firstScore A D y) (multivariateGaussian 0 A):=by
  have hi:Integrable (firstScore A D) (multivariateGaussian 0 A):=
    (IsGaussian.memLp_dual (multivariateGaussian (0:State n) A) (innerSL ℝ (coefficient A D)) 1 (by norm_num)).integrable (by norm_num)
  exact hi.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun y=>by simpa only[Real.norm_eq_abs] using hM y))

theorem centered_score_identity (A:Mat n) (D:State n) (b a:State n→ℝ)
    (hb:Measurable b) (ha:Measurable a) (B M:ℝ) (hB:∀y,|b y|≤B) (hM:∀y,|a y|≤M) (m:State n):
    (∫y,centeredTest A b a m y*firstScore A D y ∂multivariateGaussian 0 A)=
      (∫y,b (m+y)*a (m+y)*firstScore A D y ∂multivariateGaussian 0 A)-
      (∫y,b (m+y)*firstScore A D y ∂multivariateGaussian 0 A)*average A a m-
      average A b m*(∫y,a (m+y)*firstScore A D y ∂multivariateGaussian 0 A):=by
  let μ:=multivariateGaussian (0:State n) A
  have hib:=integrable_score_bdd A D (fun y=>b (m+y)) (by fun_prop) B (fun y=>hB _)
  have hia:=integrable_score_bdd A D (fun y=>a (m+y)) (by fun_prop) M (fun y=>hM _)
  have hibA:=integrable_score_bdd A D (fun y=>b (m+y)*a (m+y)) (by fun_prop) (B*M)
    (fun y=>by rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0)))
  have hiS:=integrable_score_bdd A D (fun _=>1) measurable_const 1 (fun _=>by norm_num)
  have hp (y:State n):centeredTest A b a m y*firstScore A D y=
      (b (m+y)*a (m+y)*firstScore A D y-
        (b (m+y)*firstScore A D y)*average A a m)-
        average A b m*(a (m+y)*firstScore A D y)+
        (average A b m*average A a m)*firstScore A D y:=by unfold centeredTest;ring
  simp_rw[hp]
  have h1 := integral_add ((hibA.sub (hib.mul_const (average A a m))).sub (hia.const_mul (average A b m)))
    (by simpa only[one_mul] using hiS.const_mul (average A b m*average A a m))
  have h2 := integral_sub (hibA.sub (hib.mul_const (average A a m))) (hia.const_mul (average A b m))
  have h3 := integral_sub hibA (hib.mul_const (average A a m))
  simp only [Pi.sub_apply] at h1 h2 h3
  rw[h1,h2,h3,integral_mul_const,integral_const_mul,integral_const_mul,
    firstScore_mean_zero,mul_zero,add_zero]

/-- The baseline derivative is included exactly. Neither rough test is
differentiated pointwise; the new score acts on the whole centered product. -/
theorem hasDerivAt_word {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (b a:State n→ℝ) (hb:Measurable b) (ha:Measurable a)
    (B M:ℝ) (hB:∀y,|b y|≤B) (hM:∀y,|a y|≤M) (m:State n) (θ:ℝ):
    HasDerivAt (fun s:ℝ=>word A b a (m+s•D))
      (∫y,centeredTest A b a (m+θ•D) y*firstScore A D y ∂multivariateGaussian 0 A) θ:=by
  have hprod:=hasDerivAt_average hA hD (fun y=>b y*a y) (hb.mul ha) (B*M)
    (fun y=>by rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0))) m θ
  have hbr:=hasDerivAt_average hA hD b hb B hB m θ
  have har:=hasDerivAt_average hA hD a ha M hM m θ
  convert! hprod.sub (hbr.mul har) using 1
  rw[centered_score_identity A D b a hb ha B M hB hM]
  ring

private theorem bounded_multiplier_L2 {E:Type*} [MeasurableSpace E] {μ:Measure E}
    (b r s:E→ℝ) (hb:Measurable b) (B:ℝ) (hB0:0≤B) (hB:∀y,|b y|≤B)
    (hr:MemLp r 2 μ) (hs:MemLp s 2 μ):
    |∫y,b y*r y*s y ∂μ|≤B*normTwo μ r*normTwo μ s:=by
  have hi:=hr.norm.integrable_mul hs.norm
  have hib:Integrable (fun y=>b y*r y*s y) μ:=by
    convert! (hr.integrable_mul hs).bdd_mul hb.aestronglyMeasurable
      (ae_of_all _ (fun y=>by simpa only[Real.norm_eq_abs] using hB y)) using 1
    funext y
    change b y*r y*s y=b y*(r y*s y)
    ring
  have hc:=integral_mul_normTwo_bound hr.norm hs.norm
  have hnorm: normTwo μ (fun y=>‖r y‖)=normTwo μ r:=by simp only[normTwo,Real.norm_eq_abs,sq_abs]
  have hsnorm: normTwo μ (fun y=>‖s y‖)=normTwo μ s:=by simp only[normTwo,Real.norm_eq_abs,sq_abs]
  rw[hnorm,hsnorm,abs_of_nonneg (integral_nonneg (fun y=>mul_nonneg (norm_nonneg _) (norm_nonneg _)))] at hc
  rw[←Real.norm_eq_abs]
  calc
    _≤∫y,‖b y*r y*s y‖ ∂μ:=norm_integral_le_integral_norm _
    _≤∫y,B*(‖r y‖*‖s y‖) ∂μ:=by
      apply integral_mono hib.norm (hi.const_mul B)
      intro y
      change ‖b y*r y*s y‖≤B*(‖r y‖*‖s y‖)
      rw[norm_mul,norm_mul,Real.norm_eq_abs]
      calc
        _≤(B*‖r y‖)*‖s y‖:=mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)) (norm_nonneg _)
        _=_:=by ring
    _=B*(∫y,‖r y‖*‖s y‖ ∂μ):=integral_const_mul _ _
    _≤_:=by convert! mul_le_mul_of_nonneg_left hc hB0 using 1;ring

/-- The full mean derivative (including the changing baseline) is controlled
by one new physical mean-score energy and the actual centered rough L2 leaf. -/
theorem word_mean_derivative_bound {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (b a:State n→ℝ) (hb:Measurable b) (ha:Measurable a)
    (B M:ℝ) (hB:∀y,|b y|≤B) (hM:∀y,|a y|≤M) (m:State n):
    |∫y,centeredTest A b a m y*firstScore A D y ∂multivariateGaussian 0 A|≤
      2*B*sqrt (scoreVariance A D)*normTwo (multivariateGaussian 0 A)
        (fun y=>a (m+y)-average A a m):=by
  let μ:=multivariateGaussian (0:State n) A
  have hB0:0≤B:=(abs_nonneg (b 0)).trans (hB 0)
  have hb0:|average A b m|≤B:=average_bound A b B hB m
  have ha0:|average A a m|≤M:=average_bound A a M hM m
  have hrc:MemLp (fun y=>a (m+y)-average A a m) 2 μ:=
    bounded_memLp (C:=2*M) (by fun_prop) (fun y=>(abs_sub _ _).trans (by linarith[hM (m+y)]))
  have hsc:MemLp (firstScore A D) 2 μ:=
    IsGaussian.memLp_dual μ (innerSL ℝ (coefficient A D)) 2 (by norm_num)
  have hc:=bounded_multiplier_L2 (fun y=>b (m+y)-average A b m)
    (fun y=>a (m+y)-average A a m) (firstScore A D) (by fun_prop) (2*B) (by positivity)
    (fun y=>(abs_sub _ _).trans (by linarith[hB (m+y)])) hrc hsc
  have hs:normTwo μ (firstScore A D)=sqrt (scoreVariance A D):=by
    have he:=(firstScore_even_moments hA hD 1).2
    simp only[show 2*1=2 by rfl,pow_one,GaussianScoreKernel.firstScoreMoment_one,mul_one,sq_abs] at he
    exact congrArg sqrt he
  rw[hs] at hc
  convert! hc using 1
  dsimp only [μ]
  ring

/-- The unmarked first word retains the actual centered rough L2 gain. -/
theorem word_amplitude_bound (A:Mat n) (b a:State n→ℝ) (hb:Measurable b) (ha:Measurable a)
    (B M:ℝ) (hB:∀y,|b y|≤B) (hM:∀y,|a y|≤M) (m:State n):
    |word A b a m|≤B*normTwo (multivariateGaussian 0 A) (fun y=>a (m+y)-average A a m):=by
  let μ:=multivariateGaussian (0:State n) A
  have hB0:0≤B:=(abs_nonneg (b 0)).trans (hB 0)
  have ha0:=average_bound A a M hM m
  have hbm:MemLp (fun y=>b (m+y)) 2 μ:=bounded_memLp (by fun_prop) (fun y=>hB _)
  have ham:MemLp (fun y=>a (m+y)) 2 μ:=bounded_memLp (by fun_prop) (fun y=>hM _)
  have hr:MemLp (fun y=>a (m+y)-average A a m) 2 μ:=
    bounded_memLp (C:=2*M) (by fun_prop) (fun y=>(abs_sub _ _).trans (by linarith[hM (m+y)]))
  have he:(∫y,b (m+y)*(a (m+y)-average A a m) ∂μ)=word A b a m:=by
    simp_rw[mul_sub]
    have hi:=integral_sub (hbm.integrable_mul ham) ((hbm.integrable one_le_two).mul_const (average A a m))
    simp only [Pi.mul_apply] at hi
    rw[hi,integral_mul_const]
    rfl
  rw[←he]
  exact (integral_mul_normTwo_bound hbm hr).trans
    (mul_le_mul_of_nonneg_right (normTwo_bound (by fun_prop) hB0 (fun y=>hB _)) (normTwo_nonneg _ _))

end SHE.GaussianCovarianceWord
