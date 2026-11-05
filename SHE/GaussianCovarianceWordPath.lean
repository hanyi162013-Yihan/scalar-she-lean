module

public import SHE.GaussianCovarianceWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! A single actual rank-one Gaussian covariance curve, simultaneously for
all bounded Borel tests, and the complete root/rough word derivative along
that curve. The changing rough baseline is differentiated exactly. -/
namespace SHE.GaussianCovarianceWordPath
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores
  GaussianCovarianceWord ProfileL2
open scoped InnerProductSpace NNReal
variable {n:ℕ}

def physicalCovarianceCurve (A:Mat n) (D:State n) (ν:Measure (State n)) (s:ℝ):Measure (State n):=
  rankOneGaussianLaw ν
    (normalizedCovarianceResponse (multivariateGaussian 0 A) (innerSL ℝ (coefficient A D)))
    (scoreVariance A D+s*scoreVariance A D^2).toNNReal

def measureWord (μ:Measure (State n)) (b a:State n→ℝ) (m:State n):ℝ:=
  (∫y,b (m+y)*a (m+y) ∂μ)-(∫y,b (m+y) ∂μ)*(∫y,a (m+y) ∂μ)

/-- One residual Gaussian law works for every test, so products and their
baselines use exactly the same covariance path. Its quadratic forms have
the literal physical increment `s (K D)^2`. -/
theorem exists_physical_covariance_curve {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) (hV:0<scoreVariance A D):
    ∃ν:Measure (State n), IsGaussian ν ∧
      physicalCovarianceCurve A D ν 0=multivariateGaussian 0 A ∧
      (∀(K:State n→L[ℝ] ℝ)(s:ℝ),0≤scoreVariance A D+s*scoreVariance A D^2→
        Var[K;physicalCovarianceCurve A D ν s]=Var[K;multivariateGaussian 0 A]+s*(K D)^2) ∧
      (∀(F:State n→ℝ),Measurable F→∀(M:ℝ),(∀y,|F y|≤M)→
        HasDerivAt (fun s:ℝ=>∫y,F y ∂physicalCovarianceCurve A D ν s)
          ((1/2:ℝ)*∫y,F y*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A) 0):=by
  let μ:=multivariateGaussian (0:State n) A
  let L:=innerSL ℝ (coefficient A D)
  have hMean:(∫y,L y ∂μ)=0:=firstScore_mean_zero A D
  have hVar:0<Var[L;μ]:=by rw[firstScore_variance hA hD];exact hV
  obtain ⟨hLd,ν,hν,hker,hμ⟩:=gaussian_covariance_range_factorization μ L hMean hVar
  let :IsGaussian ν:=hν
  let v:ℝ≥0:=(Var[L;μ]).toNNReal
  have hv:(v:ℝ)=Var[L;μ]:=Real.coe_toNNReal _ hVar.le
  have hv0:v≠0:=by exact_mod_cast (hv.symm ▸ hVar.ne')
  let d:=normalizedCovarianceResponse μ L
  have hμ':rankOneGaussianLaw ν d v=μ:=hμ.symm
  have hvar:Var[L;μ]=scoreVariance A D:=firstScore_variance hA hD
  have hcurve (s:ℝ):physicalCovarianceCurve A D ν s=
      rankOneGaussianLaw ν d ((v:ℝ)+s*(v:ℝ)^2).toNNReal:=by
    dsimp only[physicalCovarianceCurve,d,L,μ]
    rw[hv,hvar]
  refine ⟨ν,hν,?_,?_,?_⟩
  · rw[hcurve]
    simpa only[zero_mul,add_zero,Real.toNNReal_coe] using hμ'
  · intro K s hs
    rw[hcurve]
    have hb:=variance_rankOneGaussianLaw ν d v K
    have hp:=variance_rankOneGaussianLaw ν d ((v:ℝ)+s*(v:ℝ)^2).toNNReal K
    rw[hμ',hv,hvar] at hb
    have hs':0≤(v:ℝ)+s*(v:ℝ)^2:=by simpa only[hv,hvar] using hs
    rw[Real.coe_toNNReal _ hs'] at hp
    rw[hp,hb]
    dsimp only[d,normalizedCovarianceResponse]
    rw[map_smul,smul_eq_mul,firstScore_response hA hD]
    rw[hv,hvar]
    field_simp
    ring
  · intro F hF M hM
    have hh:=hasDerivAt_rankOne_variance ν d v hv0 F hF M hM L hLd hker
    have hg:HasDerivAt (fun s:ℝ=>(v:ℝ)+s*(v:ℝ)^2) ((v:ℝ)^2) 0:=by
      convert! (hasDerivAt_const 0 (v:ℝ)).add ((hasDerivAt_id 0).mul_const ((v:ℝ)^2)) using 1; simp
    have hh':HasDerivAt (fun w:ℝ=>∫y,F y ∂rankOneGaussianLaw ν d w.toNNReal)
        ((1/2:ℝ)*∫y,F y*GaussianAudit.secondScore v (L y) ∂rankOneGaussianLaw ν d v)
        ((v:ℝ)+0*(v:ℝ)^2):=by simpa using hh
    have hc:=hh'.comp 0 hg
    simp only[Function.comp_def] at hc
    simp_rw[←hcurve] at hc
    rw[hμ'] at hc
    convert! hc using 1
    rw[mul_assoc,←integral_mul_const]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>by
      dsimp only[GaussianAudit.secondScore,MeasurableGaussianScores.secondScore,L]
      change F y*(firstScore A D y^2-scoreVariance A D)=
        F y*((firstScore A D y^2-(v:ℝ))/(v:ℝ)^2)*(v:ℝ)^2
      rw[hv,hvar]
      field_simp)

private theorem integrable_second_bdd {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (f:State n→ℝ) (hf:Measurable f) (M:ℝ) (hM:∀y,|f y|≤M):
    Integrable (fun y=>f y*MeasurableGaussianScores.secondScore A D y) (multivariateGaussian 0 A):=by
  have hp:= (secondScore_even_moments hA hD 1).1
  have hs:MemLp (MeasurableGaussianScores.secondScore A D) 2 (multivariateGaussian 0 A):=by
    apply (memLp_two_iff_integrable_sq (by unfold MeasurableGaussianScores.secondScore MeasurableGaussianScores.firstScore; fun_prop)).mpr
    simpa only[show 2*1=2 by rfl,sq_abs] using hp
  exact (hs.integrable one_le_two).bdd_mul hf.aestronglyMeasurable
    (ae_of_all _ (fun y=>by simpa only[Real.norm_eq_abs] using hM y))

/-- The second-score derivative acts on the complete centered product; the
baseline derivative is included, and no derivative of either test occurs. -/
theorem centered_second_score_identity {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (b a:State n→ℝ) (hb:Measurable b) (ha:Measurable a) (B M:ℝ)
    (hB:∀y,|b y|≤B) (hM:∀y,|a y|≤M) (m:State n):
    (∫y,centeredTest A b a m y*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A)=
      (∫y,b (m+y)*a (m+y)*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A)-
      (∫y,b (m+y)*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A)*GaussianCovarianceWord.average A a m-
      GaussianCovarianceWord.average A b m*(∫y,a (m+y)*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A):=by
  have hib:=integrable_second_bdd hA hD (fun y=>b (m+y)) (by fun_prop) B (fun _=>hB _)
  have hia:=integrable_second_bdd hA hD (fun y=>a (m+y)) (by fun_prop) M (fun _=>hM _)
  have hibA:=integrable_second_bdd hA hD (fun y=>b (m+y)*a (m+y)) (by fun_prop) (B*M)
    (fun y=>by rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0)))
  have hiS:=integrable_second_bdd hA hD (fun _=>1) measurable_const 1 (fun _=>by norm_num)
  have hp (y:State n):centeredTest A b a m y*MeasurableGaussianScores.secondScore A D y=
      (b (m+y)*a (m+y)*MeasurableGaussianScores.secondScore A D y-
        (b (m+y)*MeasurableGaussianScores.secondScore A D y)*GaussianCovarianceWord.average A a m)-
        GaussianCovarianceWord.average A b m*(a (m+y)*MeasurableGaussianScores.secondScore A D y)+
        (GaussianCovarianceWord.average A b m*GaussianCovarianceWord.average A a m)*MeasurableGaussianScores.secondScore A D y:=by
    unfold centeredTest;ring
  simp_rw[hp]
  have h1:=integral_add ((hibA.sub (hib.mul_const (GaussianCovarianceWord.average A a m))).sub
    (hia.const_mul (GaussianCovarianceWord.average A b m)))
    (by simpa only[one_mul] using hiS.const_mul (GaussianCovarianceWord.average A b m*GaussianCovarianceWord.average A a m))
  have h2:=integral_sub (hibA.sub (hib.mul_const (GaussianCovarianceWord.average A a m)))
    (hia.const_mul (GaussianCovarianceWord.average A b m))
  have h3:=integral_sub hibA (hib.mul_const (GaussianCovarianceWord.average A a m))
  simp only[Pi.sub_apply] at h1 h2 h3
  rw[h1,h2,h3,integral_mul_const,integral_const_mul,integral_const_mul,
    secondScore_mean_zero hA hD,mul_zero,add_zero]

/-- Actual covariance differentiation of the full bounded root/rough word,
with a single physical covariance curve for the product and both baselines. -/
theorem exists_word_covariance_derivative {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) (hV:0<scoreVariance A D)
    (b a:State n→ℝ) (hb:Measurable b) (ha:Measurable a) (B M:ℝ)
    (hB:∀y,|b y|≤B) (hM:∀y,|a y|≤M) (m:State n):
    ∃ν:Measure (State n), IsGaussian ν ∧
      physicalCovarianceCurve A D ν 0=multivariateGaussian 0 A ∧
      (∀(K:State n→L[ℝ] ℝ)(s:ℝ),0≤scoreVariance A D+s*scoreVariance A D^2→
        Var[K;physicalCovarianceCurve A D ν s]=Var[K;multivariateGaussian 0 A]+s*(K D)^2) ∧
      HasDerivAt (fun s:ℝ=>measureWord (physicalCovarianceCurve A D ν s) b a m)
        ((1/2:ℝ)*∫y,centeredTest A b a m y*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A) 0:=by
  obtain ⟨ν,hν,h0,hcov,hder⟩:=exists_physical_covariance_curve hA hD hV
  refine ⟨ν,hν,h0,hcov,?_⟩
  have hba:=hder (fun y=>b (m+y)*a (m+y)) (by fun_prop) (B*M)
    (fun y=>by rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0)))
  have hbr:=hder (fun y=>b (m+y)) (by fun_prop) B (fun _=>hB _)
  have har:=hder (fun y=>a (m+y)) (by fun_prop) M (fun _=>hM _)
  have hc:=hba.sub (hbr.mul har)
  rw[h0] at hc
  convert! hc using 1
  rw[centered_second_score_identity hA hD b a hb ha B M hB hM]
  dsimp only[GaussianCovarianceWord.average]
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


theorem secondScoreMoment_one : GaussianAudit.secondScoreMoment 1=2:=by
  have h:=integral_sq_secondScore (1:ℝ≥0)
  simpa only[GaussianAudit.secondScoreMoment,GaussianAudit.secondScore,
    show 2*1=2 by rfl,NNReal.coe_one,one_pow,div_one] using h

/-- The complete rank-one covariance derivative has precisely one physical
covariance-score energy. The root and centered rough leaf can be dependent. -/
theorem word_covariance_derivative_bound {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (b a:State n→ℝ) (hb:Measurable b) (ha:Measurable a) (B M:ℝ)
    (hB:∀y,|b y|≤B) (hM:∀y,|a y|≤M) (m:State n):
    |(1/2:ℝ)*∫y,centeredTest A b a m y*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A|≤
      B*sqrt 2*scoreVariance A D*normTwo (multivariateGaussian 0 A)
        (fun y=>a (m+y)-GaussianCovarianceWord.average A a m):=by
  let μ:=multivariateGaussian (0:State n) A
  have hB0:0≤B:=(abs_nonneg (b 0)).trans (hB 0)
  have hb0:=average_bound A b B hB m
  have ha0:=average_bound A a M hM m
  have hrc:MemLp (fun y=>a (m+y)-GaussianCovarianceWord.average A a m) 2 μ:=
    bounded_memLp (C:=2*M) (by fun_prop) (fun y=>(abs_sub _ _).trans (by linarith[hM (m+y)]))
  have hsc:MemLp (MeasurableGaussianScores.secondScore A D) 2 μ:=by
    apply (memLp_two_iff_integrable_sq
      (by unfold MeasurableGaussianScores.secondScore MeasurableGaussianScores.firstScore;fun_prop)).mpr
    simpa only[show 2*1=2 by rfl,sq_abs] using (secondScore_even_moments hA hD 1).1
  have hc:=bounded_multiplier_L2 (fun y=>b (m+y)-GaussianCovarianceWord.average A b m)
    (fun y=>a (m+y)-GaussianCovarianceWord.average A a m) (MeasurableGaussianScores.secondScore A D)
    (by fun_prop) (2*B) (by positivity) (fun y=>(abs_sub _ _).trans (by linarith[hB (m+y)])) hrc hsc
  have hs:normTwo μ (MeasurableGaussianScores.secondScore A D)=sqrt 2*scoreVariance A D:=by
    have he:=(secondScore_even_moments hA hD 1).2
    simp only[show 2*1=2 by rfl,secondScoreMoment_one,sq_abs] at he
    unfold normTwo
    rw[he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (scoreVariance_nonneg hA hD)]
    ring
  rw[hs] at hc
  rw[abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1/2)]
  have hh:=mul_le_mul_of_nonneg_left hc (by norm_num:(0:ℝ)≤1/2)
  convert! hh using 1
  dsimp only[μ];ring

end SHE.GaussianCovarianceWordPath
