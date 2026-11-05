module

public import SHE.ProfileL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Genuine finite-measure averaging of dependent Gaussian word fields.
The finite heat-tree measure need not be normalized to a probability. -/
namespace SHE.FiniteGaussianAveraging
open Set MeasureTheory Real ProfileL2
variable {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y]

/-- A finite positive averaging measure costs its exact mass. All dependence
between the averaged coordinate and the output coordinate is retained. -/
theorem square_average_le (κ:Measure Y)[IsFiniteMeasure κ](μ:Measure X)[SFinite μ]
    (F:Y×X→ℝ)(hF:Measurable F)(hF2:Integrable (fun p=>F p^2) (κ.prod μ)):
    Integrable (fun x=>(∫y,F (y,x) ∂κ)^2) μ ∧
      (∫x,(∫y,F (y,x) ∂κ)^2 ∂μ)≤κ.real univ*(∫p,F p^2 ∂κ.prod μ):=by
  have hGm:Measurable (fun x=>∫y,F (y,x) ∂κ):=
    hF.stronglyMeasurable.integral_prod_left'.measurable
  have hfib:∀ᵐx ∂μ,(∫y,F (y,x) ∂κ)^2≤κ.real univ*(∫y,F (y,x)^2 ∂κ):=by
    filter_upwards[hF2.prod_left_ae] with x hx
    have hFx:MemLp (fun y=>F (y,x)) 2 κ:=
      (memLp_two_iff_integrable_sq (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx
    have hc:=integral_mul_normTwo_bound (memLp_const (1:ℝ):MemLp (fun _:Y=>(1:ℝ)) 2 κ) hFx
    simp only[one_mul] at hc
    have hh:=pow_le_pow_left₀ (abs_nonneg _) hc 2
    simpa only[sq_abs,mul_pow,normTwo_sq,one_pow,integral_const,smul_eq_mul,mul_one] using hh
  have hi:Integrable (fun x=>(∫y,F (y,x) ∂κ)^2) μ:=by
    apply (hF2.integral_prod_right.const_mul (κ.real univ)).mono' (hGm.pow_const 2).aestronglyMeasurable
    filter_upwards[hfib] with x hx
    rw[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (∫y,F (y,x) ∂κ))]
    exact hx
  refine ⟨hi,?_⟩
  calc
    _≤∫x,κ.real univ*(∫y,F (y,x)^2 ∂κ) ∂μ:=
      integral_mono_ae hi (hF2.integral_prod_right.const_mul _) hfib
    _=κ.real univ*(∫p,F p^2 ∂κ.prod μ):=by
      rw[integral_const_mul,integral_prod_symm _ hF2]

end SHE.FiniteGaussianAveraging
