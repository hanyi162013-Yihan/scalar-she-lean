module
public import SHE.GaussianContinuity
public import SHE.SmoothTestLaw

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.GaussianStandardRealization
open Set MeasureTheory ProbabilityTheory WordRecursion GaussianContinuity GaussianConvolution
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {X:Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable {n:ℕ} (C:X→PositiveCovariance n) (m:X→State n)

def value (p:X) (z:State n):State n:=m p+Matrix.toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt (C p).val) z

theorem continuous (hC:Continuous C) (hm:Continuous m):
    Continuous (fun p:X×State n=>value C m p.1 p.2):=by
  have hsqrt:Continuous (fun p:X×State n=>CFC.sqrt (C p.1).val):=
    ((continuous_positive_sqrt n).comp hC).comp continuous_fst
  have he:(fun p:X×State n=>Matrix.toEuclideanCLM (𝕜:=ℝ) (CFC.sqrt (C p.1).val) p.2)=
      fun p:X×State n=>WithLp.toLp 2 (fun i=>∑j,(CFC.sqrt (C p.1).val) i j*p.2 j):=by
    funext p
    apply (WithLp.equiv 2 (Fin n→ℝ)).injective
    exact Matrix.ofLp_toEuclideanCLM _ _
  unfold value
  apply (hm.comp continuous_fst).add
  rw [he]
  apply (PiLp.continuous_toLp 2 (fun _:Fin n=>ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ (fun j _=>
    ((((continuous_apply j).comp (continuous_apply i)).comp hsqrt).mul
      ((EuclideanSpace.proj j).continuous.comp continuous_snd)))

theorem average (p:X) (F:State n→ℝ) (hF:Continuous F):
    gaussianAverage (C p).val F (m p)=
      ∫z:State n,F (value C m p z) ∂stdGaussian (State n):=
  gaussian_integral_as_standard F hF (C p).val (m p)

variable {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsProbabilityMeasure μ]
variable (hC:Continuous C) (hm:Continuous m) (u:Ω→X) (hu:Measurable u)

def simulated (z:Ω×State n):State n:=value C m (u z.1) z.2

include hC hm hu in
theorem simulated_measurable:Measurable (simulated C m u):=
  (continuous C m hC hm).measurable.comp ((hu.comp measurable_fst).prodMk measurable_snd)

include hC hm hu in
/-- A smooth-test transition yields an actual product-space law. This
retains the random covariance and all random displacement tests inside
the original expectation, including bounded nonsmooth minima. -/
theorem hasLaw (Y:Ω→State n) (hY:Measurable Y)
    (ht:∀F:State n→ℝ,SmoothCylinders.BoundedSmooth F→
      (∫ω,F (Y ω) ∂μ)=∫ω,gaussianAverage (C (u ω)).val F (m (u ω)) ∂μ):
    HasLaw Y ((μ.prod (stdGaussian (State n))).map (simulated C m u)) μ:=by
  have hs:=simulated_measurable C m hC hm u hu
  apply SmoothTestLaw.hasLaw μ Y hY _
  intro F hF
  rw [integral_map hs.aemeasurable hF.smooth.continuous.measurable.aestronglyMeasurable]
  obtain ⟨B,hB⟩:=hF.norm_bound
  have hi:Integrable (fun z:Ω×State n=>F (simulated C m u z)) (μ.prod (stdGaussian (State n))):=
    (integrable_const B).mono' (hF.smooth.continuous.measurable.comp hs).aestronglyMeasurable
      (ae_of_all _ (fun z=>hB _))
  rw [integral_prod _ hi,ht F hF]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω=>average C m (u ω) F hF.smooth.continuous)

end SHE.GaussianStandardRealization
