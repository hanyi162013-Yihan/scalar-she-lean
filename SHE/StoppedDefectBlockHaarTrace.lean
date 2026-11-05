module

public import SHE.StoppedDefectBlockProjection
public import SHE.HeatSpanSignedHaarTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace SHE.StoppedDefectBlockHaarTrace
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores BlockDefectScores StoppedDefectBlockProjection
local instance stoppedDefectBlockHaarTrace_period:Fact (0<2*π):=⟨by positivity⟩
local instance stoppedDefectBlockHaarTrace_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

private theorem translated_basis {n g:ℕ}(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀j i,u<groupData label rep σ j i)(j:Fin g)(i:Fin n):
    StronglyMeasurable (fun x:UnitAddCircle=>synthesis label rep σ target
      (fun i=>a i+x) u Λ t hage act j (EuclideanSpace.basisFun (Fin n) ℝ i)):=by
  by_cases hij:label i=j
  · have hm:=(HeatChristoffelTransfer.continuous_translate_action.comp (continuous_id.prodMk
      (continuous_const:Continuous (fun _:UnitAddCircle=>unitHeatKernel (t i) (a i))))).stronglyMeasurable
    have hs:=hm.const_smul (1-(exp (-Λ*(σ i-u)):ℂ))
    convert! hs using 1
    funext x
    simp only [synthesis,LinearMap.comp_apply,LinearMap.restrictScalars_apply,Submodule.subtype_apply,
      defectBlockRow_basis,if_pos hij]
    change (1-(exp (-Λ*(σ i-u)):ℂ)) • unitHeatKernel (t i) (a i+x)=
      (1-(exp (-Λ*(σ i-u)):ℂ)) • HeatTorusKernel.translate x (unitHeatKernel (t i) (a i))
    rw [translate_unitHeatKernel (ht i)]
  · convert! (stronglyMeasurable_const:StronglyMeasurable (fun _:UnitAddCircle=>(0:HeatTorus.CircleL2))) using 1
    funext x
    simp only [synthesis,LinearMap.comp_apply,LinearMap.restrictScalars_apply,Submodule.subtype_apply,
      defectBlockRow_basis,if_neg hij]

/-- One genuine age block's clipped SAME-Haar score has its signed
negative-input trace under the ORIGINAL full covariance. Its own heat
age is retained, so a younger endpoint is never substituted for it. -/
theorem trace (n:ℕ):
    ∃h K θ:ℝ,0<h ∧ h≤1 ∧ 0<K ∧ 0<θ ∧
      ∀{g:ℕ}(hg:0<g)(label:Fin n→Fin g)(rep:Fin g→Fin n)(hrep:∀j,label (rep j)=j)
      (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ),0<Λ→
      ∀(t:Fin n→ℝ)(ht:∀i,0<t i),(∀i,t i≤h)→
      ∀(hage:∀i,target i-u=4*π^2*t i)(hages:∀i,σ i≤target i)
      (lower upper M:Fin g→ℝ)(A:ℝ),4*(g:ℝ)^2+1≤A→
      (∀j,0<lower j)→(∀j,lower j≤upper j)→(∀j,1≤M j)→(∀j,upper j≤M j*lower j)→
      (∀i,u+lower (label i)≤σ i)→(∀i,σ i≤u+upper (label i))→
      (∀j k,j<k→A*upper j≤lower k)→
      ∀(j:Fin g)(w N:ℝ),0<w→1≤N→(∀i,w≤groupData label rep t j i)→
      (∀i,groupData label rep t j i≤N*w)→θ*w≤1→
      ∀(c:UnitAddCircle×Domain→ℝ)(hc:Measurable c)(U ell:ℝ)
      (hcb:∀x p,0≤c (x,p)∧c (x,p)≤U),0<ell→(∀x p,ell≤c (x,p))→
      ∀{ρ:ℝ},0<ρ→ρ<1/2→∀(f g0:CircleHeat.CircleL2)(m M0:ℝ),0<m→
      (∀ᵐy∂haarAddCircle,(f y).im=0)→(∀ᵐy∂haarAddCircle,(g0 y).im=0)→
      (∀ᵐy∂haarAddCircle,m≤(f y).re∧(f y).re≤M0)→
      (∀ᵐy∂haarAddCircle,m≤(g0 y).re∧(g0 y).re≤M0)→
      ∀(act:∀j i,u<groupData label rep σ j i),
      let S:=fun x=>synthesis label rep σ target (fun i=>a i+x) u Λ t hage act j
      let V:=fun x=>stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p)) u
      let Q:=fun l:HaarNode=>fun x:UnitAddCircle=>scoreVariance (V x)
        (meanDirection (S x) (globalSignedColumn l f g0))
      Integrable (fun x=>∑'l,Q l x) haarAddCircle ∧
      (∫x,∑'l,Q l x ∂haarAddCircle)≤
        (max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2)*K*sqrt N*sqrt w*
        (signedHeatSqConstant 1 ρ m M0*StepInput.negativeEnergy 1 Λ ρ (f-g0)*
          (Λ^ρ*(θ*w)^(-(1/2:ℝ))+(θ*w)^(-(1/2:ℝ)-ρ))):=by
  obtain ⟨h,K,θ,hh,hh1,hK,hθ,hproj⟩:=translated_heat_span_projection_bound n
  refine ⟨h,K,θ,hh,hh1,hK,hθ,?_⟩
  intro g hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA
    hlo hlohi hM hratio hstlo hsthi hsep j w N hw hN htwlo htwhi hθw
    c hc U ell hcb hell hcl ρ hρ hρhalf f g0 m M0 hm hfreal hgreal hf hg0 act S V Q
  let E:=(max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2)
  have hE:0≤E:=div_nonneg (mul_nonneg
    (mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) (sq_nonneg _))
    (inv_nonneg.mpr (hlo j).le)) (half_pos hell).le
  have htj(i:Fin n):0<groupData label rep t j i:=by unfold groupData;split_ifs <;> exact ht _
  have hthj(i:Fin n):groupData label rep t j i≤h:=by unfold groupData;split_ifs <;> exact hth _
  have ha(x:UnitAddCircle):groupData label rep (fun i=>a i+x) j=(fun i=>groupData label rep a j i+x):=by
    funext i;unfold groupData;split_ifs <;> rfl
  have hpt(l:HaarNode)(x:UnitAddCircle):
      meanDirection (S x) (globalSignedColumn l f g0)∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (V x)).range ∧
      Q l x≤E*‖(heatSpan (groupData label rep t j) (fun i=>groupData label rep a j i+x)).starProjection
        (globalSignedColumn l f g0)‖^2:=by
    have hp:=score_projection hg label rep hrep σ target (fun i=>a i+x) u Λ hΛ t hage hages
      lower upper M A hA hlo hlohi hM hratio hstlo hsthi hsep (fun p=>c (x,p))
      (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb x) hell (hcl x) j (globalSignedColumn l f g0)
    simpa only [ha] using hp
  have hVp(x:UnitAddCircle):(V x).PosSemidef:=by
    rw [show V x=stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p)) u from rfl,
      ←weightedFeature_gram σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p))
      (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u]
    exact Matrix.posSemidef_gram ℝ _
  have hVm:Measurable V:=by
    have hm:=translated_feature_gram_measurable σ target a hages u hc U hcb
    convert! hm using 1
    funext x
    exact (weightedFeature_gram σ target (nativeCenter (fun i=>a i+x)) (fun p=>c (x,p))
      (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u).symm
  have hQ0(l:HaarNode)(x:UnitAddCircle):0≤Q l x:=scoreVariance_nonneg (hVp x) (hpt l x).1
  have hQi(l:HaarNode):Integrable (Q l) haarAddCircle:=by
    have hm:=scoreVariance_measurable.comp (hVm.prodMk (meanDirection_measurable S
      (translated_basis label rep σ target a u Λ t ht hage act j) (globalSignedColumn l f g0)))
    have hi:=(hproj (groupData label rep t j) (groupData label rep a j) htj hthj
      w N hw hN htwlo htwhi (globalSignedColumn l f g0)).1
    exact (hi.const_mul E).mono' hm.aestronglyMeasurable (ae_of_all _ (fun x=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (hQ0 l x)]
      exact (hpt l x).2))
  have hb(l:HaarNode):(∫x,Q l x ∂haarAddCircle)≤
      (E*K*sqrt N*sqrt w)*‖heat (θ*w) (globalSignedColumn l f g0)‖^2:=by
    have hp:=hproj (groupData label rep t j) (groupData label rep a j) htj hthj
      w N hw hN htwlo htwhi (globalSignedColumn l f g0)
    have hi:=integral_mono (hQi l) (hp.1.const_mul E) (fun x=>(hpt l x).2)
    rw [integral_const_mul] at hi
    exact hi.trans ((mul_le_mul_of_nonneg_left hp.2 hE).trans_eq (by ring))
  have hheat:=global_signed_heat (mul_pos hθ hw) hθw (by norm_num:0≤(1:ℝ)) hΛ hρ hρhalf
    f g0 m M0 hm hfreal hgreal hf hg0
  have hn(l:HaarNode):(∫x,‖Q l x‖ ∂haarAddCircle)=(∫x,Q l x ∂haarAddCircle):=
    integral_congr_ae (ae_of_all _ (fun x=>Real.norm_of_nonneg (hQ0 l x)))
  have hs:Summable (fun l:HaarNode=>∫x,‖Q l x‖ ∂haarAddCircle):=
    Summable.of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _))
      (fun l=>by rw [hn];exact hb l) (hheat.1.mul_left (E*K*sqrt N*sqrt w))
  refine ⟨FractionalEnergy.nonnegative_tsum_integrable haarAddCircle Q hQi
    (fun l=>ae_of_all _ (hQ0 l)) hs,?_⟩
  rw [←integral_tsum_of_summable_integral_norm hQi hs]
  calc
    _≤∑'l:HaarNode,(E*K*sqrt N*sqrt w)*‖heat (θ*w) (globalSignedColumn l f g0)‖^2:=
      (hs.congr hn).tsum_le_tsum hb (hheat.1.mul_left _)
    _=(E*K*sqrt N*sqrt w)*(∑'l:HaarNode,‖heat (θ*w) (globalSignedColumn l f g0)‖^2):=tsum_mul_left
    _≤_:=mul_le_mul_of_nonneg_left hheat.2 (by positivity)

end SHE.StoppedDefectBlockHaarTrace
