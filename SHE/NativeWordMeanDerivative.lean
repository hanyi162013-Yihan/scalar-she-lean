module

public import SHE.GaussianWordMeanDerivative
public import SHE.NativeMeanScoreKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The instantaneous n=1 bounded old-root/rough-leaf Gaussian mean derivative, integrated
against actual native physical covariance and actual damped signed means.
Relative centers, coefficient profiles, and inputs may depend on all the
same parameters. The scalar rough marginal variance bound is explicit. -/
namespace SHE.NativeWordMeanDerivative
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  HeatTorus HeatTorusKernel GaussianGramScore GaussianIncrement MeasurableGaussianScores
  NativeMeanFields NativeMeanAveraging NativeMeanScoreKernel MeasurableGeneralizedInverse
  GaussianWordFields GaussianWordMeanDerivative NativeGaussianFirstWord GaussianAudit NativeOldRoot
open scoped InnerProductSpace NNReal
local instance : Fact (0 < 2*Real.pi):=⟨by positivity⟩
variable [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2]

/-- This controls the actual Gaussian word derivative, not a surrogate score
kernel. The sole input remains in its physical heat image, and all other
parameter dependence is retained in the covariance kernel. -/
theorem native_firstWord_mean_derivative_energy (n:ℕ) (hn:0<n):
    ∃h C:ℝ,0<h ∧ h≤1 ∧ 0<C ∧
      ∀{X:Type*}[MeasurableSpace X](μ:Measure X)[SFinite μ]
      (target:Fin n→ℝ)(a:X→Fin n→UnitAddCircle)(ha:∀i,Measurable (fun y=>a y i))
      (u Λ:ℝ),0<Λ→∀(t:Fin n→ℝ)(ht:∀i,0<t i),(∀i,t i≤h)→
      ∀(hage:∀i,target i-u=4*π^2*t i)(s:ℝ)(hs:0<s)(hmin:∀i,u+s≤target i)
      (c:(X×UnitAddCircle)×Domain→ℝ)(hc:Measurable c)(U ell:ℝ)
      (hcb:∀p r,0≤c (p,r) ∧ c (p,r)≤U),0<ell→(∀p r,ell≤c (p,r))→
      ∀(d:X→HeatTorus.CircleL2),Measurable d→Integrable (fun y=>‖d y‖^2) μ→
      ∀(m:X×UnitAddCircle→State n),Measurable m→
      ∀(v:ℝ≥0)(f f' b:ℝ→ℝ)(K L:State n→L[ℝ] ℝ)(A0 ν M H β W:ℝ),
      0≤A0→0≤ν→(∀z,HasDerivAt f (f' z) z)→(∀z,|f z|≤A0)→(∀z,|f' z|≤A0*ν)→
      Measurable b→(∀z,|b z|≤M)→0≤H→0≤β→(∀z w,|b z-b w|≤H*|z-w|^β)→
      (∀p,Var[L;multivariateGaussian 0 (covarianceField target a c u p)]≤W)→
      let act:∀i,u<target i:=fun i=>by linarith[hmin i]
      let A:=covarianceField target a c u
      let D:=directionField target a u Λ t hage act d
      let T:=4*A0*rootClipMass v ν*sqrt (H^2*W^β*gaussianAbsMoment (2*β))
      Integrable (fun p=>(firstMeanScore (A p) (D p) v f b K L (m p))^2)
        (μ.prod haarAddCircle) ∧
      (∫p,(firstMeanScore (A p) (D p) v f b K L (m p))^2 ∂μ.prod haarAddCircle)≤
        T^2*((C/ell)*(sqrt s)⁻¹)*(∫y,‖d y‖^2 ∂μ):=by
  obtain ⟨h,C,hh,hh1,hC,he⟩:=native_mean_score_one_input n hn
  refine ⟨h,C,hh,hh1,hC,?_⟩
  intro X _ μ _ target a ha u Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d hd hid
    m hm v f f' b K L A0 ν M H β W hA0 hν hf hfb hfD hb hbB hH hβ hholder hW
  let act:∀i,u<target i:=fun i=>by linarith[hmin i]
  let A:=covarianceField target a c u
  let D:=directionField target a u Λ t hage act d
  let T:=4*A0*rootClipMass v ν*sqrt (H^2*W^β*gaussianAbsMoment (2*β))
  have hAm:Measurable A:=covarianceField_measurable target a ha c hc u
  have hDm:Measurable D:=directionField_measurable target a ha u Λ t ht hage act d hd
  have hApos (p:X×UnitAddCircle):(A p).PosSemidef:=
    StoppedGaussianFields.covariance_posSemidef (NativeMeanFields.observations target a ha) c (fun _=>u) p
      (hc.comp (measurable_const.prodMk measurable_id)) (hcb p) (fun _=>le_rfl)
  have hDr (p:X×UnitAddCircle):D p∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A p)).range:=
    physical_mean_direction_mem_range target (fun i=>a p.1 i+p.2) u Λ hΛ t hage act s hs hmin
      (fun r=>c (p,r)) (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb p) hell (hcl p) (d p.1)
  have hmean:=he μ target a ha u Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d hd hid
  have hV:Integrable (fun p:X×UnitAddCircle=>scoreVariance (A p) (D p)) (μ.prod haarAddCircle):=hmean.1
  have hword:=firstMeanScore_square_integral (μ.prod haarAddCircle) A hAm hApos D m hDm hm hDr hV
    v f f' b K L A0 ν M H β W hA0 hν hf hfb hfD hb hbB hH hβ hholder hW
  refine ⟨hword.1,hword.2.trans ?_⟩
  convert! mul_le_mul_of_nonneg_left hmean.2 (sq_nonneg T) using 1
  ring

end SHE.NativeWordMeanDerivative
