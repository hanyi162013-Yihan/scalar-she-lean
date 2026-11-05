module

public import SHE.ScalarGaussianSemigroup

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.ScalarGaussianHeatEquation
open Set MeasureTheory ProbabilityTheory Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup
open scoped NNReal ENNReal

/-- The actual scalar Gaussian variance equation, including its exact
factor one half and derivatives of the displayed Gaussian average. -/
theorem hasDerivAt_heat {a : ℝ→ℝ} (ha : BoundedSmooth a) {v : ℝ} (hv : 0<v) (x : ℝ) :
    HasDerivAt (fun w : ℝ=>heat w.toNNReal a x)
      ((1/2:ℝ)*iteratedDeriv 2 (heat v.toNNReal a) x) v := by
  obtain ⟨B,hB⟩:=ha.norm_bound
  have hb (z : ℝ) : |a z|≤B:=by simpa only [Real.norm_eq_abs] using hB z
  have hn : v.toNNReal≠0:=by positivity
  have hs:=hasDerivAt_deriv_gaussianConvolution v.toNNReal hn a ha.smooth.continuous.measurable B hb x
  have hh:=hasDerivAt_gaussian_variance_integral v.toNNReal hn (fun z=>a (x+z))
    (ha.smooth.continuous.measurable.comp (measurable_const.add measurable_id)) B (fun z=>hb (x+z))
  rw [Real.coe_toNNReal _ hv.le,←hs.deriv] at hh
  simpa only [heat,gaussianConvolution,show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hh

/-- Every finite spatial derivative satisfies the same actual variance
heat equation. This is a consequence of proved derivative commutation,
not an assumed Gaussian regularity package. -/
theorem hasDerivAt_jet {a : ℝ→ℝ} (ha : BoundedSmooth a) {v : ℝ} (hv : 0<v) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun w : ℝ=>iteratedDeriv n (heat w.toNNReal a) x)
      ((1/2:ℝ)*iteratedDeriv (n+2) (heat v.toNNReal a) x) v := by
  have hh:=hasDerivAt_heat (iteratedDeriv_boundedSmooth ha n) hv x
  have he : (fun w : ℝ=>iteratedDeriv n (heat w.toNNReal a) x)=
      (fun w : ℝ=>heat w.toNNReal (iteratedDeriv n a) x):=by
    funext w
    rw [iteratedDeriv_heat w.toNNReal ha n]
  rw [←he] at hh
  have hj : iteratedDeriv 2 (heat v.toNNReal (iteratedDeriv n a))=
      iteratedDeriv (n+2) (heat v.toNNReal a) := by
    rw [←iteratedDeriv_heat v.toNNReal ha n]
    simp only [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
  rw [hj] at hh
  exact hh

end SHE.ScalarGaussianHeatEquation
