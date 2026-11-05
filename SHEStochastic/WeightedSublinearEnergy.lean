module

public import SHE.FractionalMoment
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.WeightedSublinearEnergy
open MeasureTheory Filter
open scoped ENNReal

/-- Interpolation for a kernel difference: only its uniform cap and its
ordinary squared energy are needed. Unlike `kernel_power`, this does not
require positivity or mass one of the underlying signed kernel. -/
theorem energy_interpolation {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (h f : X → ℝ≥0∞) (hh : AEMeasurable h ν) (hf : AEMeasurable f ν)
    (L : ℝ≥0∞) (hcap : ∀ᵐ x ∂ν, h x ≤ L)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∫⁻ x, h x * f x ^ β ∂ν) ≤
      L ^ β * ((∫⁻ x, h x ∂ν) ^ (1 - β) * (∫⁻ x, f x ∂ν) ^ β) := by
  have hpoint : ∀ᵐ x ∂ν, h x * f x ^ β ≤ L ^ β * (h x ^ (1 - β) * f x ^ β) := by
    filter_upwards [hcap] with x hx
    have he : h x = h x ^ β * h x ^ (1 - β) := by
      rw [← ENNReal.rpow_add_of_nonneg β (1 - β) hβ (sub_nonneg.mpr hβ1)]
      simp only [add_sub_cancel, ENNReal.rpow_one]
    calc
      _ = (h x ^ β * h x ^ (1 - β)) * f x ^ β := by rw [← he]
      _ ≤ (L ^ β * h x ^ (1 - β)) * f x ^ β := by gcongr
      _ = _ := mul_assoc _ _ _
  calc
    _ ≤ ∫⁻ x, L ^ β * (h x ^ (1 - β) * f x ^ β) ∂ν := lintegral_mono_ae hpoint
    _ = L ^ β * ∫⁻ x, h x ^ (1 - β) * f x ^ β ∂ν :=
      lintegral_const_mul'' _ ((hh.pow_const _).mul (hf.pow_const _))
    _ ≤ _ := mul_le_mul_right
      (ENNReal.lintegral_mul_norm_pow_le hh hf (sub_nonneg.mpr hβ1) hβ (by ring)) _

/-- Sublinear coefficient growth paired with an arbitrary kernel energy.
This is the common deterministic step for time and spatial increments. -/
theorem energy_with_growth {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (h f g : X → ℝ≥0∞) (hh : AEMeasurable h ν) (hf : AEMeasurable f ν)
    (A L Q : ℝ≥0∞) (hcap : ∀ᵐ x ∂ν, h x ≤ L) (henergy : (∫⁻ x, h x ∂ν) ≤ Q)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hg : ∀ᵐ x ∂ν, g x ≤ A * (1 + f x ^ β)) :
    (∫⁻ x, h x * g x ∂ν) ≤
      A * (Q + L ^ β * (Q ^ (1 - β) * (∫⁻ x, f x ∂ν) ^ β)) := by
  calc
    _ ≤ ∫⁻ x, A * (h x + h x * f x ^ β) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hg] with x hx
      exact (mul_le_mul_right hx (h x)).trans_eq (by ring)
    _ = A * ((∫⁻ x, h x ∂ν) + ∫⁻ x, h x * f x ^ β ∂ν) := by
      rw [lintegral_const_mul'' A (f := fun x ↦ h x + h x * f x ^ β)
        (hh.add (hh.mul (hf.pow_const β))), lintegral_add_left' hh]
    _ ≤ A * (Q + L ^ β * ((∫⁻ x, h x ∂ν) ^ (1 - β) * (∫⁻ x, f x ∂ν) ^ β)) :=
      mul_le_mul_right (add_le_add henergy (energy_interpolation ν h f hh hf L hcap hβ hβ1)) A
    _ ≤ _ := by gcongr

/-- The spatial Hölder estimate behind the unbounded heat-row bound.
A normalized kernel bounded by L gains L^(1+β), rather than L².
With the heat bound L ~ r^(-1/2), this gives r^(-(1+β)/2). -/
theorem kernel_power {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (k f : X → ℝ≥0∞) (hk : AEMeasurable k ν) (hf : AEMeasurable f ν)
    (L : ℝ≥0∞) (hcap : ∀ᵐ x ∂ν, k x ≤ L) (hmass : (∫⁻ x, k x ∂ν) = 1)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∫⁻ x, k x ^ 2 * f x ^ β ∂ν) ≤ L ^ (1 + β) * (∫⁻ x, f x ∂ν) ^ β := by
  have hfactor (x : X) : k x ^ 2 = k x ^ (1 + β) * k x ^ (1 - β) := by
    rw [← ENNReal.rpow_add_of_nonneg (1 + β) (1 - β) (by linarith) (by linarith),
      show (1 + β) + (1 - β) = 2 by ring, ENNReal.rpow_two]
  have hpoint : ∀ᵐ x ∂ν, k x ^ 2 * f x ^ β ≤
      L ^ (1 + β) * (k x ^ (1 - β) * f x ^ β) := by
    filter_upwards [hcap] with x hx
    rw [hfactor]
    calc
      _ ≤ (L ^ (1 + β) * k x ^ (1 - β)) * f x ^ β := by
        gcongr
      _ = _ := mul_assoc _ _ _
  have hh := ENNReal.lintegral_mul_norm_pow_le hk hf (sub_nonneg.mpr hβ1) hβ (by ring)
  rw [hmass, ENNReal.one_rpow, one_mul] at hh
  calc
    _ ≤ ∫⁻ x, L ^ (1 + β) * (k x ^ (1 - β) * f x ^ β) ∂ν := lintegral_mono_ae hpoint
    _ = L ^ (1 + β) * ∫⁻ x, k x ^ (1 - β) * f x ^ β ∂ν :=
      lintegral_const_mul'' _ ((hk.pow_const _).mul (hf.pow_const _))
    _ ≤ _ := mul_le_mul_right hh _

/-- The full squared-coefficient energy estimate, including its constant
part. The growth premise is pointwise and can be supplied by a Hölder
coefficient; the conclusion charges only the L²-state energy. -/
theorem with_growth {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (k f g : X → ℝ≥0∞) (hk : AEMeasurable k ν) (hf : AEMeasurable f ν)
    (A L : ℝ≥0∞) (hcap : ∀ᵐ x ∂ν, k x ≤ L) (hmass : (∫⁻ x, k x ∂ν) = 1)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hg : ∀ᵐ x ∂ν, g x ≤ A * (1 + f x ^ β)) :
    (∫⁻ x, k x ^ 2 * g x ∂ν) ≤ A * (L + L ^ (1 + β) * (∫⁻ x, f x ∂ν) ^ β) := by
  have hbase : (∫⁻ x, k x ^ 2 ∂ν) ≤ L := by
    calc
      _ ≤ ∫⁻ x, L * k x ∂ν := lintegral_mono_ae (hcap.mono fun x hx ↦ by
        rw [pow_two]
        exact mul_le_mul_left hx (k x))
      _ = _ := by rw [lintegral_const_mul'' L hk, hmass, mul_one]
  have hweight := kernel_power ν k f hk hf L hcap hmass hβ hβ1
  calc
    _ ≤ ∫⁻ x, A * (k x ^ 2 + k x ^ 2 * f x ^ β) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hg] with x hx
      calc
        _ ≤ k x ^ 2 * (A * (1 + f x ^ β)) := mul_le_mul_right hx _
        _ = _ := by ring
    _ = A * ((∫⁻ x, k x ^ 2 ∂ν) + ∫⁻ x, k x ^ 2 * f x ^ β ∂ν) := by
      rw [lintegral_const_mul'' A (f := fun x ↦ k x ^ 2 + k x ^ 2 * f x ^ β)
          ((hk.pow_const 2).add ((hk.pow_const 2).mul (hf.pow_const β))),
        lintegral_add_left' (hk.pow_const 2)]
    _ ≤ _ := mul_le_mul_right (add_le_add hbase hweight) A

end SHEStochastic.WeightedSublinearEnergy
