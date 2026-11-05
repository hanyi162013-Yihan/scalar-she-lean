module

public import SHE.GaussianWordCovarianceIntegral
public import SHE.ProfileReserveAffine

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

/-! Genuine joint mean/covariance differentiation and absolute continuity
of the complete centered Gaussian word. The fixed positive reserve supplies
the diagonal chain rule; the base mean is arbitrary. -/
namespace SHE.GaussianWordAffine
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianProfileMark
  GaussianRangeSmooth GaussianConvolution GaussianCovarianceWord
  GaussianWordCovarianceIntegral MeasurableGaussianScores
open scoped NNReal InnerProductSpace Matrix.Norms.L2Operator
variable {n:ℕ}{X:Type*}[MeasurableSpace X]

def meanMark (A:Matrix (Fin n) (Fin n) ℝ)(D:State n)(b a:State n→ℝ)(z:State n):ℝ:=
  ∫y,centeredTest A b a z y*firstScore A D y ∂multivariateGaussian 0 A

def covarianceMark (μ:Measure X)(A:Matrix (Fin n) (Fin n) ℝ)
    (e:X→ℝ)(v:X→State n)(b a:State n→ℝ)(z:State n):ℝ:=
  (1/2:ℝ)*∫x,e x*(∫y,centeredTest A b a z y*secondScore A (v x) y
    ∂multivariateGaussian 0 A) ∂μ

/-- Full centered-word derivative along the actual affine-mean Gaussian
profile. Both partial derivatives are proved for bounded Borel tests. -/
theorem hasDerivAt_profile_word_affine
    (μ:Measure X){ell:ℝ}(hell:0<ell)(c:ℝ→X→ℝ)(e:X→ℝ)(v:X→State n){θ:ℝ}
    (hv:Measurable v)(henergy:Integrable (fun x=>‖v x‖^2) μ)
    (hc:∀r,AEStronglyMeasurable (c r) μ)(hci:∀r,Integrable (fun x=>|c r x| *‖v x‖^2) μ)
    (hclower:∀r,∀ᵐx ∂μ,ell≤c r x)(he:Measurable e)(g:X→ℝ)
    (hg0:∀ᵐx ∂μ,0≤g x)(hgi:Integrable (fun x=>g x*‖v x‖^2) μ)
    (hlip:∀ᵐx ∂μ,LipschitzWith (Real.nnabs (g x)) (fun r=>c r x))
    (hdiff:∀ᵐx ∂μ,HasDerivAt (fun r=>c r x) (e x) θ)
    (Q:ProfileReserve (fun r=>profileCovariance μ (c r) v)){K:ℝ≥0}
    (hK:LipschitzWith K (fun r=>(Q.residual r).val))
    (b a:State n→ℝ)(hb:Measurable b)(ha:Measurable a)(B M:ℝ)
    (hB:∀y,|b y|≤B)(hM:∀y,|a y|≤M)(base D:State n)
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (profileCovariance μ (c θ) v)).range):
    HasDerivAt (fun r=>word (profileCovariance μ (c r) v) b a (base+r•D))
      (covarianceMark μ (profileCovariance μ (c θ) v) e v b a (base+θ•D)+
        meanMark (profileCovariance μ (c θ) v) D b a (base+θ•D)) θ:=by
  let A:=profileCovariance μ (c θ) v
  let z:=base+θ•D
  have hiA:=profileCovariance_integrable μ (c θ) v (hc θ) hv.aestronglyMeasurable (hci θ)
  have hA:A.PosSemidef:=profileCovariance_positive μ (c θ) v hiA
    ((hclower θ).mono (fun _ hx=>hell.le.trans hx))
  have hrange:=ae_frame_mem_profile_range μ v hv.aestronglyMeasurable henergy
    (c θ) (hc θ) (hci θ) hell (hclower θ)
  have hE:Integrable (fun x=>|e x| *‖v x‖^2) μ:=by
    apply hgi.mono' ((continuous_abs.measurable.comp he).mul (hv.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards[hlip,hdiff,hg0] with x hx hd hg
    change ‖|e x| *‖v x‖^2‖≤g x*‖v x‖^2
    rw[Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    have hh:=hd.le_of_lipschitz hx
    rw[Real.norm_eq_abs,Real.coe_nnabs,abs_of_nonneg hg] at hh
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  have hprod:∀y,|b y*a y|≤B*M:=fun y=>by
    rw[abs_mul]
    exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0))
  have hp:=hasDerivAt_profile_borel_of_uniform_floor μ hell c e v hv.aestronglyMeasurable henergy
    hc hci hclower he.aestronglyMeasurable g hg0 hgi hlip hdiff (fun y=>b y*a y) (hb.mul ha) (B*M) hprod z
  have hbr:=hasDerivAt_profile_borel_of_uniform_floor μ hell c e v hv.aestronglyMeasurable henergy
    hc hci hclower he.aestronglyMeasurable g hg0 hgi hlip hdiff b hb B hB z
  have har:=hasDerivAt_profile_borel_of_uniform_floor μ hell c e v hv.aestronglyMeasurable henergy
    hc hci hclower he.aestronglyMeasurable g hg0 hgi hlip hdiff a ha M hM z
  have hpm:=hasDerivAt_average hA hD (fun y=>b y*a y) (hb.mul ha) (B*M) hprod z 0
  have hbm:=hasDerivAt_average hA hD b hb B hB z 0
  have ham:=hasDerivAt_average hA hD a ha M hM z 0
  simp only[zero_smul,add_zero] at hpm hbm ham
  have hpt:=Q.hasDerivAt_affine_of_partials hK _ (hb.mul ha) (B*M) hprod base D hD hp hpm
  have hbt:=Q.hasDerivAt_affine_of_partials hK b hb B hB base D hD hbr hbm
  have hat:=Q.hasDerivAt_affine_of_partials hK a ha M hM base D hD har ham
  convert! hpt.sub (hbt.mul hat) using 1
  dsimp only[covarianceMark,meanMark]
  rw[outer_centered_identity μ hA v hv hrange e he hE b a hb ha B M hB hM z,
    centered_score_identity A D b a hb ha B M hB hM z]
  dsimp only[rawMark,GaussianCovarianceWord.average,gaussianAverage,A,z]
  ring

/-- The complete word curve is genuinely Lipschitz, including its product
of changing Gaussian baselines. Constants are coarse and used only for FTC. -/
theorem exists_lipschitz_word_affine {A:ℝ→Matrix (Fin n) (Fin n) ℝ}
    (Q:ProfileReserve A){K:ℝ≥0}(hK:LipschitzWith K (fun r=>(Q.residual r).val))
    (b a:State n→ℝ)(hb:Measurable b)(ha:Measurable a)(B M:ℝ)
    (hB:∀y,|b y|≤B)(hM:∀y,|a y|≤M)(base D:State n)
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A 0)).range):
    ∃L:ℝ≥0,LipschitzWith L (fun θ=>word (A θ) b a (base+θ•D)):=by
  have hB0:0≤B:=(abs_nonneg (b 0)).trans (hB 0)
  have hM0:0≤M:=(abs_nonneg (a 0)).trans (hM 0)
  have hprod:∀y,|b y*a y|≤B*M:=fun y=>by
    rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) hB0
  obtain ⟨Lp,hp⟩:=Q.exists_lipschitz_affine hK (fun y=>b y*a y) (hb.mul ha) (B*M) hprod base D hD
  obtain ⟨Lb,hbr⟩:=Q.exists_lipschitz_affine hK b hb B hB base D hD
  obtain ⟨La,har⟩:=Q.exists_lipschitz_affine hK a ha M hM base D hD
  let T:ℝ:=(Lp:ℝ)+B*La+M*Lb
  have hT:0≤T:=by dsimp[T];positivity
  refine ⟨Real.nnabs T,LipschitzWith.of_dist_le_mul (fun θ η=>?_)⟩
  rw[Real.coe_nnabs,abs_of_nonneg hT,Real.dist_eq]
  let p:=fun r=>GaussianCovarianceWord.average (A r) (fun y=>b y*a y) (base+r•D)
  let br:=fun r=>GaussianCovarianceWord.average (A r) b (base+r•D)
  let ar:=fun r=>GaussianCovarianceWord.average (A r) a (base+r•D)
  have hp':|p θ-p η|≤(Lp:ℝ)*dist θ η:=hp.dist_le_mul θ η
  have hb':|br θ-br η|≤(Lb:ℝ)*dist θ η:=hbr.dist_le_mul θ η
  have ha':|ar θ-ar η|≤(La:ℝ)*dist θ η:=har.dist_le_mul θ η
  have hbe:=average_bound (A θ) b B hB (base+θ•D)
  have hae:=average_bound (A η) a M hM (base+η•D)
  change |(p θ-br θ*ar θ)-(p η-br η*ar η)|≤T*dist θ η
  calc
    _=|(p θ-p η)-(br θ*(ar θ-ar η)+(br θ-br η)*ar η)|:=by congr 1;ring
    _≤|p θ-p η|+|br θ*(ar θ-ar η)+(br θ-br η)*ar η|:=abs_sub _ _
    _≤|p θ-p η|+(|br θ| *|ar θ-ar η|+|br θ-br η| *|ar η|):=by
      gcongr
      simpa only[abs_mul] using abs_add_le (br θ*(ar θ-ar η)) ((br θ-br η)*ar η)
    _≤(Lp:ℝ)*dist θ η+(B*((La:ℝ)*dist θ η)+((Lb:ℝ)*dist θ η)*M):=by gcongr
    _=T*dist θ η:=by dsimp[T];ring

/-- The actual total marked word derivative integrates to the exact word
endpoint difference; interval integrability follows from the proved reserve. -/
theorem integral_word_affine {A:ℝ→Matrix (Fin n) (Fin n) ℝ}
    (Q:ProfileReserve A){K:ℝ≥0}(hK:LipschitzWith K (fun r=>(Q.residual r).val))
    (b a:State n→ℝ)(hb:Measurable b)(ha:Measurable a)(B M:ℝ)
    (hB:∀y,|b y|≤B)(hM:∀y,|a y|≤M)(base D:State n)
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A 0)).range)(mark:ℝ→ℝ)
    (hd:∀ᵐθ ∂volume,HasDerivAt (fun r=>word (A r) b a (base+r•D)) (mark θ) θ)(r s:ℝ):
    IntervalIntegrable mark volume r s ∧
      (∫θ in r..s,mark θ)=word (A s) b a (base+s•D)-word (A r) b a (base+r•D):=by
  obtain ⟨L,hL⟩:=exists_lipschitz_word_affine Q hK b a hb ha B M hB hM base D hD
  exact LipschitzIntegralIdentity.integral_eq_sub hL hd r s

end SHE.GaussianWordAffine
