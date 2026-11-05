module
public import SHE.FiniteGaussianAveraging
public import Mathlib.MeasureTheory.Group.Arithmetic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.TimeTranslationAverage
open Set MeasureTheory Real
variable {P Ω:Type*}[MeasurableSpace P][MeasurableSpace Ω]
variable (κ:Measure P)[IsFiniteMeasure κ](μ:Measure Ω)[SFinite μ]

/-- True global clock-translation averaging. The original random input
is translated before the finite positive history/kernel average; its
L2 energy is preserved, giving the SQUARE of the actual kernel mass.
There is no pointwise energy cap and no exchange of square and time
integral without its required mass factor. -/
theorem square (a:P→ℝ)(ha:Measurable a)(F:ℝ×Ω→ℝ)(hF:Measurable F)
    (hF2:Integrable (fun z=>F z^2) (volume.prod μ)):
    Integrable (fun z:ℝ×Ω=>(∫p,F (z.1-a p,z.2) ∂κ)^2) (volume.prod μ) ∧
      (∫z:ℝ×Ω,(∫p,F (z.1-a p,z.2) ∂κ)^2 ∂volume.prod μ)≤
        (κ.real univ)^2*(∫z:ℝ×Ω,F z^2 ∂volume.prod μ):=by
  let G:P×(ℝ×Ω)→ℝ:=fun z=>F (z.2.1-a z.1,z.2.2)
  have hG:Measurable G:=hF.comp
    ((measurable_snd.fst.sub (ha.comp measurable_fst)).prodMk measurable_snd.snd)
  have htrans(p:P):MeasurePreserving (fun z:ℝ×Ω=>(z.1-a p,z.2)) (volume.prod μ) (volume.prod μ):=
    (measurePreserving_sub_right volume (a p)).prod (MeasurePreserving.id μ)
  have hGi(p:P):Integrable (fun z:ℝ×Ω=>G (p,z)^2) (volume.prod μ):=by
    exact ((htrans p).integrable_comp hF2.aestronglyMeasurable).mpr hF2
  have hmass(p:P):(∫z:ℝ×Ω,G (p,z)^2 ∂volume.prod μ)=
      ∫z:ℝ×Ω,F z^2 ∂volume.prod μ:=by
    rw [integral_prod_symm _ (hGi p),integral_prod_symm _ hF2]
    apply integral_congr_ae
    filter_upwards with ω
    exact integral_sub_right_eq_self (μ:=volume) (fun t:ℝ=>F (t,ω)^2) (a p)
  have hG2:Integrable (fun z:P×(ℝ×Ω)=>G z^2) (κ.prod (volume.prod μ)):=by
    apply (integrable_prod_iff (hG.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hGi,?_⟩
    have he:(fun p:P=>∫z:ℝ×Ω,‖G (p,z)^2‖ ∂volume.prod μ)=
        fun _=>∫z:ℝ×Ω,F z^2 ∂volume.prod μ:=by
      funext p
      calc
        _=(∫z:ℝ×Ω,G (p,z)^2 ∂volume.prod μ):=integral_congr_ae
          (ae_of_all _ (fun z=>Real.norm_of_nonneg (sq_nonneg (G (p,z)))))
        _=_:=hmass p
    rw [he]
    exact integrable_const _
  have h:=FiniteGaussianAveraging.square_average_le κ (volume.prod μ) G hG hG2
  refine ⟨h.1,?_⟩
  have he:(∫z:P×(ℝ×Ω),G z^2 ∂κ.prod (volume.prod μ))=
      κ.real univ*(∫z:ℝ×Ω,F z^2 ∂volume.prod μ):=by
    rw [integral_prod _ hG2]
    simp_rw [hmass]
    simp only [integral_const,smul_eq_mul]
  exact h.2.trans_eq (by rw [he];ring)

end SHE.TimeTranslationAverage
