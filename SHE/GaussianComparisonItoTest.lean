module

public import SHE.FiniteComparisonTest
public import SHE.ParameterSmoothContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace SHE.GaussianComparisonItoTest
open Set MeasureTheory GaussianIncrement GaussianItoTest SmoothCylinders UniformSmooth
open GaussianConvolution ProbabilityTheory
variable {n : ℕ} (W : CovarianceEndpoint.EndpointWindow n) (F : WordRecursion.State n→ℝ)

def value (t : ℝ) (z : WordRecursion.State (n+n)) : ℝ :=
  backward W F t (FiniteComparisonTest.left n z)-backward W F t (FiniteComparisonTest.right n z)

def derivative (t : ℝ) (z : WordRecursion.State (n+n)) : ℝ :=
  backwardDerivative W F t (FiniteComparisonTest.left n z)-
    backwardDerivative W F t (FiniteComparisonTest.right n z)

/-- The actual two-copy Gaussian backward test is uniformly smooth in
its physical finite state, including a singular or vanishing reserve. -/
theorem uniformSmooth (hF : BoundedSmooth F) : UniformBoundedSmooth (value W F) := by
  have hs : UniformBoundedSmooth (fun t : ℝ=>backward W F t) :=
    (UniformBoundedSmooth.fixed hF).average
      (fun t=>multivariateGaussian (0:WordRecursion.State n) (W.path t).val) (fun _=>inferInstance)
  exact (hs.comp_right (FiniteComparisonTest.left n)).sub (hs.comp_right (FiniteComparisonTest.right n))

/-- Ordinary finite-dimensional Itô applies to the genuine paired
Gaussian test. The reserve may vanish at the terminal time; the true
inverse-square-root heat majorant supplies its time envelope. -/
theorem regular (hF : BoundedSmooth F) : RegularTest W.left W.right (value W F) (derivative W F) := by
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨L,hL⟩:=hF.fderiv.norm_bound
  obtain ⟨B,hB⟩:=hF.fderiv.fderiv.norm_bound
  obtain ⟨K,hK0,hHess⟩:=hF.hessian_lipschitz
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0)
  have hreg : RegularTest W.left W.right (backward W F) (backwardDerivative W F) := backward_regular (n:=n) W (hF.smooth.of_le (by simp)) hM hL hB hB0 hK0 hHess
  have hs := uniformSmooth W F hF
  have hleft : Continuous (fun p : ℝ×WordRecursion.State (n+n)=>(p.1,FiniteComparisonTest.left n p.2)) :=
    continuous_fst.prodMk ((FiniteComparisonTest.left n).continuous.comp continuous_snd)
  have hright : Continuous (fun p : ℝ×WordRecursion.State (n+n)=>(p.1,FiniteComparisonTest.right n p.2)) :=
    continuous_fst.prodMk ((FiniteComparisonTest.right n).continuous.comp continuous_snd)
  have hbase:=GaussianContinuity.continuous_gaussian_average (n:=n) F hF.smooth.continuous hM
  have hlc:=hbase.comp ((W.continuous_path.comp continuous_fst).prodMk
    ((FiniteComparisonTest.left n).continuous.comp continuous_snd))
  have hrc:=hbase.comp ((W.continuous_path.comp continuous_fst).prodMk
    ((FiniteComparisonTest.right n).continuous.comp continuous_snd))
  have hcont : Continuous (fun p : ℝ×WordRecursion.State (n+n)=>value W F p.1 p.2) := by
    change Continuous (fun p : ℝ×WordRecursion.State (n+n)=>
      (∫ y : WordRecursion.State n,F (FiniteComparisonTest.left n p.2+y) ∂multivariateGaussian 0 (W.path p.1).val)-
      (∫ y : WordRecursion.State n,F (FiniteComparisonTest.right n p.2+y) ∂multivariateGaussian 0 (W.path p.1).val))
    exact hlc.sub hrc
  obtain ⟨BB,hBB0,hBB⟩:=hs.fderiv.fderiv.norm_bound
  refine ⟨hcont,fun t=>(hs.smooth t).of_le (by simp),
    ParameterSmoothContinuity.continuous_fderiv _ hcont (fun t=>(hs.smooth t).of_le (by simp)) hBB0 hBB,
    ParameterSmoothContinuity.continuous_hessian _ hcont hs,?_,?_,?_,?_,?_,?_⟩
  · intro z
    exact (hreg.time_absolutelyContinuous (FiniteComparisonTest.left n z)).sub
      (hreg.time_absolutelyContinuous (FiniteComparisonTest.right n z))
  · filter_upwards [hreg.time_derivative] with t ht htm z
    exact (ht htm (FiniteComparisonTest.left n z)).sub (ht htm (FiniteComparisonTest.right n z))
  · unfold derivative
    have hdl := hreg.derivative_measurable.comp hleft.measurable
    have hdr := hreg.derivative_measurable.comp hright.measurable
    exact hdl.sub hdr
  · intro t
    unfold derivative
    have hcl := (hreg.derivative_state_continuous t).comp (FiniteComparisonTest.left n).continuous
    have hcr := (hreg.derivative_state_continuous t).comp (FiniteComparisonTest.right n).continuous
    exact hcl.sub hcr
  · obtain ⟨m,hm,hmb⟩:=hreg.derivative_envelope
    refine ⟨fun t=>2*m t,hm.const_mul 2,fun t ht z=>?_⟩
    unfold derivative
    exact (norm_sub_le _ _).trans (by linarith [hmb t ht (FiniteComparisonTest.left n z),hmb t ht (FiniteComparisonTest.right n z)])
  · obtain ⟨M,hM0,hM⟩:=hs.norm_bound
    obtain ⟨L,hL0,hL⟩:=hs.fderiv.norm_bound
    exact ⟨M,L,BB,fun t z=>⟨hM t z,hL t z,hBB t z⟩⟩

end SHE.GaussianComparisonItoTest
