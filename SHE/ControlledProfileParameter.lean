module

public import SHE.ControlledProfilePointwise
public import SHE.RealCurveL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Genuine measurable parameter derivatives of the separate controlled
damped-mean profile. Coarse domination and sharp spatial L² derivative
bounds are derived independently, uniformly in the damping scale. -/
namespace SHE.ControlledProfile
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance ProfileStability
  ProfilePointwise ProfileParameter ProfileL2
open scoped NNReal Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable (P : CanonicalCovariance.ProfileParameters)

def derivative (Λ : ℝ) (u d : CircleL2) (p : Domain × ℝ) : ℝ :=
  deriv (fun θ => profile P Λ u d (θ, p.1)) p.2

theorem profile_curve_measurable (Λ : ℝ) (u d : CircleL2) :
    Measurable (fun p : Domain × ℝ => profile P Λ u d (p.2, p.1)) :=
  (profile_measurable P Λ u d).comp measurable_swap

theorem derivative_measurable {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2) :
    Measurable (derivative P Λ u d) :=
  MeasuredRealCurves.derivative_measurable
    (fun p => (profile_curve_lipschitz P hΛ u d hsmallPoint p).continuous)
    (profile_curve_measurable P Λ u d)

theorem ae_hasDerivAt {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (μ : Measure Domain) [SFinite μ] :
    ∀ᵐ θ ∂volume, ∀ᵐ p ∂μ,
      HasDerivAt (fun η => profile P Λ u d (η, p)) (derivative P Λ u d (p, θ)) θ :=
  MeasuredRealCurves.ae_ae_hasDerivAt μ (profile_curve_measurable P Λ u d)
    (profile_curve_lipschitz P hΛ u d hsmallPoint)

theorem derivative_bound {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (p : Domain) (θ : ℝ) :
    |derivative P Λ u d (p, θ)| ≤ curveBound P.lower P.holder P.exponent P.horizon d p :=
  MeasuredRealCurves.derivative_bound (profile_curve_lipschitz P hΛ u d hsmallPoint) p θ

theorem spatial_curve_lipschitz {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {r : ℝ} (hr : r ∈ Ioc 0 P.horizon) (x : HeatCircle) :
    LipschitzWith ⟨pointwiseConstant P.lower P.holder P.exponent r d,
      pointwiseConstant_nonneg P.lower_pos.le P.holder_nonneg hr.1.le d⟩
      (fun θ => profile P Λ u d (θ, (r, x))) := by
  have h := profile_curve_lipschitz P hΛ u d hsmallPoint (r, x)
  simpa only [curveBound, ite_eq_left hr] using h

/-- The sharp controlled-profile L² finite differences transfer to the
ordinary scalar derivative; the coarser spatial Lipschitz constant is used
only for genuine dominated convergence of difference quotients. -/
theorem derivative_l2_bound {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 1) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    {r θ : ℝ} (hr : r ∈ Ioc 0 P.horizon)
    (hd : ∀ᵐ x ∂haarAddCircle, HasDerivAt (fun η => profile P Λ u d (η, (r, x)))
      (derivative P Λ u d ((r, x), θ)) θ) :
    MemLp (fun x => derivative P Λ u d ((r, x), θ)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => derivative P Λ u d ((r, x), θ)) ≤
        2 * (meanConstant P.lower P.holder P.exponent * ‖d‖) * r ^ ((P.exponent - 1) / 4) := by
  have hm : Measurable (fun p : HeatCircle × ℝ => profile P Λ u d (p.2, (r, p.1))) :=
    (profile_curve_measurable P Λ u d).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  apply RealCurveL2.derivative_normTwo_bound haarAddCircle hm
    (spatial_curve_lipschitz P hΛ u d hsmallPoint hr)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg (meanConstant_nonneg (β := P.exponent) P.lower_pos.le P.holder_nonneg)
        (norm_nonneg d))) (Real.rpow_nonneg hr.1.le _)) _ hd
  intro η ξ
  have h := profile_l2_stability P hΛ u d η ξ hsmallL2 hr
  convert! h using 1
  ring

theorem ae_derivative_l2 {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 1) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2) :
    ∀ᵐ θ ∂volume, ∀ᵐ r ∂volume.restrict (Ioc 0 P.horizon),
      MemLp (fun x => derivative P Λ u d ((r, x), θ)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => derivative P Λ u d ((r, x), θ)) ≤
        2 * (meanConstant P.lower P.holder P.exponent * ‖d‖) * r ^ ((P.exponent - 1) / 4) := by
  have he := ae_hasDerivAt P hΛ u d hsmallPoint
    ((volume.restrict (Ioc 0 P.horizon)).prod (haarAddCircle (T := 2 * Real.pi)))
  filter_upwards [he] with θ hθ
  filter_upwards [Measure.ae_ae_of_ae_prod hθ, ae_restrict_mem measurableSet_Ioc] with r hr hrmem
  exact derivative_l2_bound P hΛ u d hsmallPoint hsmallL2 hrmem hr

end SHE.ControlledProfile
