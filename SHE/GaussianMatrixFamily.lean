module
public import SHE.GaussianMatrixCurve
public import SHE.UniformAffineSmooth
public import SHE.GaussianParameterContinuity
public import SHE.MeasurableDerivatives
public import SHE.LocalizedItoTest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SHE.GaussianMatrixFamily
open Set MeasureTheory ProbabilityTheory GaussianContinuity GaussianMatrixCurve
open GaussianConvolution GaussianTaylorAverage GaussianTaylor SmoothCylinders UniformSmooth
open scoped ENNReal NNReal
abbrev State (n : ℕ) := WordRecursion.State n
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] {n : ℕ}

structure Family (X : Type*) [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X] (n : ℕ) where
  left : ℝ
  right : ℝ
  curve : X → GaussianMatrixCurve.Curve n
  left_eq : ∀ p, (curve p).left = left
  right_eq : ∀ p, (curve p).right = right
  path_measurable : Measurable (fun z : X × ℝ => (curve z.1).path z.2)
  path_parameter_continuous : ∀ t, Continuous (fun p => (curve p).path t)
  density_measurable : Measurable (fun z : X × ℝ => (curve z.1).density z.2)
  density_parameter_continuous : ∀ᵐ t : ℝ ∂volume.restrict (Ioc left right),
    Continuous (fun p => (curve p).density t)
  center : X → State n
  center_continuous : Continuous center

variable (S : Family X n) (F : State n → ℝ)

def shifted (p : X) (z : State n) : ℝ := F (z + S.center p)
def value (p : X) (t : ℝ) (z : State n) : ℝ :=
  GaussianMatrixCurve.backward (S.curve p) (shifted S F p) t z
def derivative (p : X) (t : ℝ) (z : State n) : ℝ :=
  GaussianMatrixCurve.timeDerivative (S.curve p) (shifted S F p) t z

theorem value_eq (p : X) (t : ℝ) (z : State n) :
    value S F p t z = gaussianAverage ((S.curve p).path t).val F (z + S.center p) := by
  unfold value GaussianMatrixCurve.backward shifted gaussianAverage
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  abel

theorem uniform_shifted (hF : BoundedSmooth F) : UniformBoundedSmooth (shifted S F) := by
  have hh := UniformAffineSmooth.comp_affine (UniformBoundedSmooth.fixed (P:=X) hF)
    (fun _ => ContinuousLinearMap.id ℝ (State n)) S.center (K:=1) zero_le_one
    (fun _ => ContinuousLinearMap.norm_id_le)
  convert! hh using 1

include S in
theorem uniform_value (hF : BoundedSmooth F) :
    UniformBoundedSmooth (fun p : X × ℝ => value S F p.1 p.2) := by
  have hs := uniform_shifted S F hF
  have hh : UniformBoundedSmooth (fun p : X × ℝ => shifted S F p.1) := by
    exact ⟨fun p => hs.smooth p.1, fun k => by
      obtain ⟨B,hB,hBb⟩ := hs.bounds k
      exact ⟨B,hB,fun p z => hBb p.1 z⟩⟩
  exact hh.average (fun p => multivariateGaussian 0 ((S.curve p.1).path p.2).val) (fun _ => inferInstance)

theorem smoothTimeTest (hF : BoundedSmooth F) (p : X) :
    LocalizedItoTest.SmoothTimeTest S.left S.right (value S F p) (derivative S F p) := by
  have hs := uniform_value S F hF
  have hu : UniformBoundedSmooth (value S F p) := by
    exact ⟨fun t => hs.smooth (p,t),fun k => by
      obtain ⟨B,hB,hBb⟩ := hs.bounds k
      exact ⟨B,hB,fun t z => hBb (p,t) z⟩⟩
  have hh := GaussianMatrixCurve.regular_boundedSmooth (S.curve p) ((uniform_shifted S F hF).boundedSmooth p)
  rw [S.left_eq p,S.right_eq p] at hh
  refine ⟨hh.continuous,hu,hh.time_absolutelyContinuous,hh.time_derivative,
    hh.derivative_measurable,hh.derivative_state_continuous,?_⟩
  obtain ⟨e,hei,heb⟩ := hh.derivative_envelope
  refine ⟨e,hei,fun t ht => ?_⟩
  have he0 : 0 ≤ e t := (norm_nonneg _).trans (heb t ht 0)
  exact ⟨he0,fun z => (heb t ht z).trans (le_mul_of_one_le_right he0 (by nlinarith [norm_nonneg z]))⟩

theorem value_measurable (hF : BoundedSmooth F) :
    Measurable (fun p : (X × ℝ) × State n => value S F p.1.1 p.1.2 p.2) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  have hc := GaussianContinuity.continuous_gaussian_average F hF.smooth.continuous hM
  have hmap : Measurable (fun p : (X × ℝ) × State n =>
      ((S.curve p.1.1).path p.1.2,p.2+S.center p.1.1)) :=
    (S.path_measurable.comp measurable_fst).prodMk
      (measurable_snd.add (S.center_continuous.measurable.comp measurable_fst.fst))
  have hh := hc.measurable.comp hmap
  convert! hh using 1
  funext p
  exact value_eq S F p.1.1 p.1.2 p.2

attribute [local irreducible] value

theorem gradient_measurable (hF : BoundedSmooth F) :
    Measurable (fun p : X × (ℝ × State n) => fderiv ℝ (value S F p.1 p.2.1) p.2.2) := by
  have hm := MeasurableDerivatives.fderiv_measurable (n:=n) (G:=ℝ)
    (F:=fun p:X×ℝ=>value S F p.1 p.2) (value_measurable S F hF)
    (fun p => ((uniform_value S F hF).smooth p).differentiable (by simp))
  have hpair : Measurable (fun p:X×(ℝ×State n)=>((p.1,p.2.1),p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  convert! hm.comp hpair using 1

theorem hessian_measurable (hF : BoundedSmooth F) :
    Measurable (fun p : X × (ℝ × State n) => hessian (value S F p.1 p.2.1) p.2.2) := by
  have hm := MeasurableDerivatives.hessian_measurable (n:=n)
    (F:=fun p:X×ℝ=>value S F p.1 p.2) (value_measurable S F hF)
    (fun p => ((uniform_value S F hF).smooth p).of_le (by simp))
  have hpair : Measurable (fun p:X×(ℝ×State n)=>((p.1,p.2.1),p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  convert! hm.comp hpair using 1

theorem value_parameter_continuous (hF : BoundedSmooth F) (t : ℝ) :
    Continuous (fun p : X × State n => value S F p.1 t p.2) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  have hh := (GaussianContinuity.continuous_gaussian_average F hF.smooth.continuous hM).comp
    (((S.path_parameter_continuous t).comp continuous_fst).prodMk
      (continuous_snd.add (S.center_continuous.comp continuous_fst)))
  convert! hh using 1
  funext p
  exact value_eq S F p.1 t p.2

theorem fixed_uniform (hF : BoundedSmooth F) (t : ℝ) :
    UniformBoundedSmooth (fun p : X => value S F p t) := by
  have hs := uniform_value S F hF
  exact ⟨fun p => hs.smooth (p,t),fun k => by
    obtain ⟨B,hB,hBb⟩ := hs.bounds k
    exact ⟨B,hB,fun p z => hBb (p,t) z⟩⟩

theorem gradient_parameter_continuous (hF : BoundedSmooth F) (t : ℝ) :
    Continuous (fun p : X × State n => fderiv ℝ (value S F p.1 t) p.2) := by
  have hs := fixed_uniform S F hF t
  obtain ⟨B,hB,hBb⟩ := hs.fderiv.fderiv.norm_bound
  exact ParameterSmoothContinuity.continuous_fderiv _ (value_parameter_continuous S F hF t)
    (fun p => (hs.smooth p).of_le (by simp)) hB hBb

theorem hessian_parameter_continuous (hF : BoundedSmooth F) (t : ℝ) :
    Continuous (fun p : X × State n => hessian (value S F p.1 t) p.2) :=
  ParameterSmoothContinuity.continuous_hessian _ (value_parameter_continuous S F hF t)
    (fixed_uniform S F hF t)

theorem derivative_parameter_continuous (hF : BoundedSmooth F) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioc S.left S.right),
      Continuous (fun p : X × State n => derivative S F p.1 t p.2) := by
  filter_upwards [S.density_parameter_continuous] with t ht
  have hH := hessian_parameter_continuous S F hF t
  unfold derivative GaussianMatrixCurve.timeDerivative covarianceAction
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hh := ((((continuous_apply j).comp (continuous_apply i)).comp ht).comp continuous_fst).mul
    ((hH.clm_apply (continuous_const (y:=EuclideanSpace.basisFun (Fin n) ℝ i))).clm_apply
      (continuous_const (y:=EuclideanSpace.basisFun (Fin n) ℝ j)))
  convert! hh using 1
  funext p
  simp only [Function.comp_apply, Pi.mul_apply]
  congr 3
  unfold value
  congr 1

end SHE.GaussianMatrixFamily
