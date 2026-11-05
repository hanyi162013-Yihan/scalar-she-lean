module

public import SHE.ProfilePointwise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Pointwise scalar-profile stability for prescribed physical mean fields.
The heat-type bound is only on the means; Gaussian covariance transfer and
nonlinear profile absorption are proved, not assumed. -/
namespace SHE.ProfileMeanPointwise
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile
  ProfileStability ProfilePointwise
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem scalar_profile_pointwise_stability
    {a : ℝ → ℝ} {φ ψ c d : ℝ × HeatCircle → ℝ} {ell M Ua H β h D : ℝ}
    (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hD : 0 ≤ D) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hmean : ∀ r ∈ Ioc 0 h, ∀ x, |φ (r, x) - ψ (r, x)| ≤
      Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * D)
    (hsmall : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 2) / 4) *
      h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a φ c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a ψ d r x) :
    ∀ r ∈ Ioc 0 h, ∀ x, |c (r, x) - d (r, x)| ≤
      2 * (meanConstant ell H β * Real.sqrt (1 + heatConstant) * D) * r ^ ((β - 2) / 4) := by
  have hcb' : ∀ p, |c p| ≤ M := fun p => by
    rw [abs_of_nonneg (hell.le.trans (hcb p).1)]
    exact (hcb p).2
  have hdb' : ∀ p, |d p| ≤ M := fun p => by
    rw [abs_of_nonneg (hell.le.trans (hdb p).1)]
    exact (hdb p).2
  apply spatial_weighted_absorption (a := (β - 2) / 4) (b := (β - 2) / 4)
    (θ := β / 4) hc hd (by linarith) (by linarith) (by positivity) (by ring)
    hh hh1 (by positivity [meanConstant_nonneg (β := β) hell.le hH])
    (varianceConstant_nonneg hell.le hH) hM hcb' hdb'
    (by simpa only [memoryConstant, mul_assoc, mul_left_comm, mul_comm] using hsmall)
  intro r hr x
  rw [hcf r hr x, hdf r hr x]
  have he := profileUpdate_two_inputs (φ := φ) (ψ := ψ) ha hc hd hell hM hH hβ.le hβ1
    hr.1 (hr.2.trans hh1) haB hholder
    (fun _ _ _ => (hcb _).1) (fun _ _ _ => (hcb _).2)
    (fun _ _ _ => (hdb _).1) (fun _ _ _ => (hdb _).2) x
  have hm := mul_le_mul_of_nonneg_left (hmean r hr x)
    (mul_nonneg (meanConstant_nonneg (β := β) hell.le hH)
      (Real.rpow_nonneg hr.1.le ((β - 1) / 4)))
  have hp : r ^ ((β - 1) / 4) * r ^ (-(1 / 4 : ℝ)) = r ^ ((β - 2) / 4) := by
    rw [← Real.rpow_add hr.1]
    congr 1
    ring
  calc
    _ ≤ _ := he
    _ ≤ (meanConstant ell H β * r ^ ((β - 1) / 4)) *
        (Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * D) +
        (varianceConstant ell H β * r ^ ((β - 2) / 4)) *
          |varianceMap c r x - varianceMap d r x| := add_le_add hm le_rfl
    _ = _ := by
      have hmul : (meanConstant ell H β * r ^ ((β - 1) / 4)) *
          (Real.sqrt (1 + heatConstant) * r ^ (-(1 / 4 : ℝ)) * D) =
          (meanConstant ell H β * Real.sqrt (1 + heatConstant) * D) * r ^ ((β - 2) / 4) := by
        calc
          _ = (meanConstant ell H β * Real.sqrt (1 + heatConstant) * D) *
              (r ^ ((β - 1) / 4) * r ^ (-(1 / 4 : ℝ))) := by ring
          _ = _ := by rw [hp]
      rw [hmul]

end SHE.ProfileMeanPointwise
