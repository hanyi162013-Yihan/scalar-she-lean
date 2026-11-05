module

public import SHEStochastic.FourierDiagonalFlow
public import SHE.ParameterSmoothContinuity
public import SHE.FiniteCovariancePullback

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.FourierDecayItoTest
open MeasureTheory Filter Set SHE SHE.GaussianItoTest SHE.UniformSmooth
open FourierDiagonalFlow FourierCylinderGenerator
open scoped NNReal ContDiff Topology

variable {d : ℕ} (F : State d → ℝ) (hF : ContDiff ℝ 2 F) (hs : HasCompactSupport F)

theorem derivative_identity (n : Fin d → ℤ) (t : ℝ) (z : State d) :
    fderiv ℝ F (raw n t z) (rawDerivative n t z) = heatDrift F hF hs n (raw n t z) := by
  rw [heatDrift_apply]
  simp only [rawDerivative, ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.smul_apply, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  change (-(n i : ℝ) ^ 2 * Real.exp (-t * (n i : ℝ) ^ 2)) *
    fderiv ℝ F (raw n t z) (z i • EuclideanSpace.basisFun (Fin d) ℝ i) = _
  rw [map_smul, raw_apply]
  ring

theorem hasDerivAt_raw_value (n : Fin d → ℤ) (t : ℝ) (z : State d) :
    HasDerivAt (fun r ↦ F (raw n r z)) (heatDrift F hF hs n (raw n t z)) t := by
  have hz := (hasDerivAt_raw n t).clm_apply (hasDerivAt_const t z)
  have hz' : HasDerivAt (fun r ↦ raw n r z) (rawDerivative n t z) t := by
    simpa only [map_zero, add_zero] using hz
  have hh := ((hF.differentiable (by norm_num) (raw n t z)).hasFDerivAt).comp_hasDerivAt t hz'
  rw [derivative_identity F hF hs] at hh
  exact hh

def value (H : ℝ) (n : Fin d → ℤ) (t : ℝ) (z : State d) : ℝ := F (clamped H n t z)

def derivative (H : ℝ) (n : Fin d → ℤ) (t : ℝ) (z : State d) : ℝ :=
  heatDrift F hF hs n (clamped H n t z)

include hs in
theorem hessian_entry (hSmooth : ContDiff ℝ ∞ F) (H : ℝ≥0) (n : Fin d → ℤ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) (z : State d) (i j : Fin d) :
    GaussianTaylor.hessian (value F H n t) z (EuclideanSpace.basisFun (Fin d) ℝ i)
      (EuclideanSpace.basisFun (Fin d) ℝ j) =
      (Real.exp (-t * (n i : ℝ) ^ 2) * Real.exp (-t * (n j : ℝ) ^ 2)) *
        GaussianTaylor.hessian F (clamped H n t z) (EuclideanSpace.basisFun (Fin d) ℝ i)
          (EuclideanSpace.basisFun (Fin d) ℝ j) := by
  have hcl : clamped H n t = raw n t := congrArg (raw n) (ClampedAbsoluteContinuity.of_mem ht)
  have hb := SmoothLinearFamily.boundedSmooth_of_compact hSmooth hs
  change GaussianTaylor.hessian (fun w ↦ F (clamped H n t w)) z _ _ = _
  rw [FiniteCovariancePullback.hessian_comp _ hb, hcl, raw_basis, raw_basis]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Compact smooth tests pulled back by the finite Fourier heat flow
meet the EXISTING finite Ito interface. All state derivative bounds,
time absolute continuity and the bounded heat-drift envelope are proved. -/
theorem regular (hSmooth : ContDiff ℝ ∞ F) (H : ℝ≥0) (n : Fin d → ℤ) :
    RegularTest 0 H (value F H n) (derivative F hF hs H n) := by
  have hbounded := SmoothLinearFamily.boundedSmooth_of_compact hSmooth hs
  have hu := uniformSmooth hbounded H n
  have hflow : Continuous (fun p : ℝ × State d ↦ clamped H n p.1 p.2) :=
    ((continuous_clamped H n).comp continuous_fst).clm_apply continuous_snd
  have hc : Continuous (fun p : ℝ × State d ↦ value F H n p.1 p.2) := hSmooth.continuous.comp hflow
  obtain ⟨M, hM0, hM⟩ := hu.norm_bound
  obtain ⟨L, hL0, hL⟩ := hu.fderiv.norm_bound
  obtain ⟨B, hB0, hB⟩ := hu.fderiv.fderiv.norm_bound
  refine ⟨hc, fun t ↦ (hu.smooth t).of_le (by simp),
    ParameterSmoothContinuity.continuous_fderiv _ hc (fun t ↦ (hu.smooth t).of_le (by simp)) hB0 hB,
    ParameterSmoothContinuity.continuous_hessian _ hc hu, ?_, ?_, ?_, ?_, ?_,
    ⟨M, L, B, fun t z ↦ ⟨hM t z, hL t z, hB t z⟩⟩⟩
  · intro z
    have hx : ContDiff ℝ ∞ (fun r ↦ F (raw n r z)) :=
      hSmooth.comp ((contDiff_raw n).clm_apply contDiff_const)
    have ha := (hx.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval (a := 0) (b := (H : ℝ))
    exact ClampedAbsoluteContinuity.extension H.property ha 0 H
  · apply Eventually.of_forall
    intro t ht z
    have he : (fun r ↦ value F H n r z) =ᶠ[𝓝 t] (fun r ↦ F (raw n r z)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      change F (raw n (ClampedAbsoluteContinuity.clamp 0 H r) z) = F (raw n r z)
      rw [ClampedAbsoluteContinuity.of_mem ⟨hr.1.le, hr.2.le⟩]
    have hcl : clamped H n t = raw n t := congrArg (raw n)
      (ClampedAbsoluteContinuity.of_mem ⟨ht.1.le, ht.2.le⟩)
    change HasDerivAt (fun r ↦ value F H n r z) (heatDrift F hF hs n (clamped H n t z)) t
    rw [hcl]
    exact (hasDerivAt_raw_value F hF hs n t z).congr_of_eventuallyEq he
  · exact ((heatDrift F hF hs n).continuous.comp hflow).measurable
  · intro t
    exact (heatDrift F hF hs n).continuous.comp (clamped H n t).continuous
  · exact ⟨fun _ ↦ ‖heatDrift F hF hs n‖, intervalIntegrable_const,
      fun _ _ z ↦ (heatDrift F hF hs n).norm_coe_le_norm _⟩

end SHEStochastic.FourierDecayItoTest
