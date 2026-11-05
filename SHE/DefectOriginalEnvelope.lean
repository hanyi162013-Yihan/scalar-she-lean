module
public import SHE.DefectOldTimeMass
public import SHE.DefectGapKernelReal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.DefectOriginalEnvelope
open Set MeasureTheory Real AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry HistoryProductMeasure OrderedGapCoordinates
open scoped BigOperators
open Classical
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)

def edge (T:ℝ)(k:ℕ)(t:Fin k→ℝ):ℝ:=T-∑i,gaps T k t i

def value (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (T Λ ρ A0 ν:ℝ)(k:ℕ)(f:ℝ→ℝ)(p:(Fin k→ℝ)×ℝ):ℝ:=
  DefectOldTimeMass.weight L P ell C k A0 ν p.1*
    (if R.base<p.2 ∧ p.2≤edge T k p.1 then
      DefectGapKernelMass.realKernel Λ ρ k (gaps T k p.1) (edge T k p.1-p.2)*f p.2 else 0)

/-- Honest original old/current-time joint L1 for the full point norm
envelope. Boundedness of f is used only here for applicability; the
quantitative convolution and its energy keep the actual f throughout. -/
theorem integrable (P:CanonicalCovariance.ProfileParameters){ell Λ ρ h:ℝ}
    (hell:0<ell)(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(T:ℝ)(hT:∀x,L.terminal x=T)(hpos:R.base<T)
    (hspan:T-R.base≤h)(k:ℕ)(A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (f:ℝ→ℝ)(hf:Measurable f)(hn:∀q,0≤f q)(B:ℝ)(hb:∀q,f q≤B):
    Measurable (value L P ell C T Λ ρ A0 ν k f) ∧
      (∀p,0≤value L P ell C T Λ ρ A0 ν k f p) ∧
      Integrable (value L P ell C T Λ ρ A0 ν k f)
        ((Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))).prod volume):=by
  let W:=DefectOldTimeMass.weight L P ell C k A0 ν
  let K:=DefectGapKernelMass.realKernel Λ ρ k
  let E:=value L P ell C T Λ ρ A0 ν k f
  have hW:=DefectOldTimeMass.mass L P hell C hC T hT hpos k A0 ν hA0 hν
  have hs:Measurable (edge T k):=measurable_const.sub
    (Finset.measurable_sum _ (fun i _=>(measurable_pi_apply i).comp (gaps_measurable T k)))
  have hmap:Measurable (fun p:(Fin k→ℝ)×ℝ=>(gaps T k p.1,edge T k p.1-p.2)):=
    ((gaps_measurable T k).comp measurable_fst).prodMk ((hs.comp measurable_fst).sub measurable_snd)
  have hK:=(DefectGapKernelReal.measurable Λ ρ k).comp hmap
  have hset:MeasurableSet {p:(Fin k→ℝ)×ℝ|R.base<p.2 ∧ p.2≤edge T k p.1}:=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hs.comp measurable_fst))
  have hm:Measurable E:=(hW.1.comp measurable_fst).mul
    ((hK.mul (hf.comp measurable_snd)).ite hset measurable_const)
  have hnE(p:(Fin k→ℝ)×ℝ):0≤E p:=by
    apply mul_nonneg (hW.2.1 p.1)
    split_ifs with hp
    · exact mul_nonneg (DefectGapMixtureIntegral.realKernel_nonneg (ρ:=ρ) hΛ.le k _
        (sub_nonneg.mpr hp.2)) (hn _)
    · exact le_refl 0
  have hB:0≤B:=(hn 0).trans (hb 0)
  let D:=DefectGapKernelMass.cost Λ ρ h k
  have hsec(t:Fin k→ℝ):Integrable (fun q:ℝ=>E (t,q)) volume ∧
      (∫q:ℝ,‖E (t,q)‖)≤W t*(B*D):=by
    by_cases hp:StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0))
    · have ho:ordered R.base T k t:=(StrictHistoryOrder.iff_ordered L T hT hpos k t 0 (fun _=>0)).mp hp
      have hd:((∀i,0<gaps T k t i) ∧ (∑i,gaps T k t i)<T-R.base):=(ordered_iff R.base T k t).mp ho
      have hsum:0≤∑i,gaps T k t i:=Finset.sum_nonneg (fun i _=>(hd.1 i).le)
      have hab:R.base≤edge T k t:=by dsimp only [edge];linarith only [hd.2]
      have hlen:edge T k t-R.base≤h:=by dsimp only [edge];linarith only [hspan,hsum]
      have hc:=DefectGapKernelReal.current hΛ hρ hρ1 hab hlen k (gaps T k t)
      have hqmap:Measurable (fun q:ℝ=>(gaps T k t,edge T k t-q)):=
        measurable_const.prodMk (measurable_const.sub measurable_id)
      have hkm:=(DefectGapKernelReal.measurable Λ ρ k).comp hqmap
      have hEind:(fun q:ℝ=>E (t,q))=fun q:ℝ=>W t*
          (Ioc R.base (edge T k t)).indicator
            (fun q=>K (gaps T k t) (edge T k t-q)*f q) q:=by
        funext q
        by_cases hq:R.base<q ∧ q≤edge T k t
        · simp only [E,value,W,K,Set.indicator,Set.mem_Ioc,if_pos hq]
        · simp only [E,value,W,K,Set.indicator,Set.mem_Ioc,if_neg hq]
      have hki:IntegrableOn (fun q:ℝ=>K (gaps T k t) (edge T k t-q)*f q)
          (Ioc R.base (edge T k t)) volume:=by
        apply (hc.1.mul_const B).mono' (hkm.mul hf).aestronglyMeasurable
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
        have hk0:=DefectGapMixtureIntegral.realKernel_nonneg (ρ:=ρ) hΛ.le k (gaps T k t) (sub_nonneg.mpr hq.2)
        change ‖K (gaps T k t) (edge T k t-q)*f q‖≤K (gaps T k t) (edge T k t-q)*B
        rw [Real.norm_of_nonneg (mul_nonneg hk0 (hn q))]
        exact mul_le_mul_of_nonneg_left (hb q) hk0
      have hei:Integrable (fun q:ℝ=>E (t,q)) volume:=by
        have hh:=((integrable_indicator_iff measurableSet_Ioc).mpr hki).const_mul (W t)
        rw [hEind]
        exact hh
      refine ⟨hei,?_⟩
      have he:(∫q:ℝ,‖E (t,q)‖)=W t*
          (∫q:ℝ,K (gaps T k t) (edge T k t-q)*f q
            ∂volume.restrict (Ioc R.base (edge T k t))):=by
        calc
          _=∫q:ℝ,E (t,q):=integral_congr_ae (ae_of_all _ (fun q=>Real.norm_of_nonneg (hnE (t,q))))
          _=_:=by
            rw [hEind,integral_const_mul,integral_indicator measurableSet_Ioc]
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (hW.2.1 t)
      have hcomp:(∫q:ℝ,K (gaps T k t) (edge T k t-q)*f q
          ∂volume.restrict (Ioc R.base (edge T k t)))≤
          (∫q:ℝ,K (gaps T k t) (edge T k t-q)
            ∂volume.restrict (Ioc R.base (edge T k t)))*B:=by
        rw [←integral_mul_const]
        apply integral_mono_ae hki (hc.1.mul_const B)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
        exact mul_le_mul_of_nonneg_left (hb q)
          (DefectGapMixtureIntegral.realKernel_nonneg (ρ:=ρ) hΛ.le k _ (sub_nonneg.mpr hq.2))
      exact hcomp.trans ((mul_le_mul_of_nonneg_right hc.2 hB).trans_eq (mul_comm _ _))
    · have he:∀q:ℝ,E (t,q)=0:=by
        intro q
        change (if StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0)) then _ else 0)*_=0
        rw [if_neg hp,zero_mul]
      constructor
      · have h0:=integrable_zero ℝ ℝ (volume:Measure ℝ)
        have he0:(0:ℝ→ℝ)=ᵐ[volume] (fun q:ℝ=>E (t,q)):=by
          filter_upwards with q
          simpa only [Pi.zero_apply] using (he q).symm
        exact h0.congr he0
      · simp only [he,norm_zero,integral_zero,W,DefectOldTimeMass.weight,if_neg hp,zero_mul,le_refl]
  refine ⟨hm,hnE,?_⟩
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t=>(hsec t).1),?_⟩
  apply (hW.2.2.1.mul_const (B*D)).mono'
    hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (integral_nonneg (fun q=>norm_nonneg (E (t,q))))]
  exact (hsec t).2
end SHE.DefectOriginalEnvelope
