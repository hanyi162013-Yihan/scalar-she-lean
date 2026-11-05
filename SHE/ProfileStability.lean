module

public import SHE.ProfileL2
public import SHE.ScalarProfileFixedPoint

@[expose] public section
set_option autoImplicit false

/-! Genuine scalar one-input profile stability in spatial L². -/
noncomputable section
namespace SHE.ProfileStability
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile ProfileL2

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def meanConstant (ell H β : ℝ) : ℝ :=
  H * GaussianAudit.gaussianAbsMoment (β + 1) * (lowerConstant * ell) ^ ((β - 1) / 2)

def varianceConstant (ell H β : ℝ) : ℝ :=
  ((H / 2) * GaussianAudit.secondScoreAbsIncrementMoment β) *
    (lowerConstant * ell) ^ (β / 2 - 1)

def memoryConstant (ell H β : ℝ) : ℝ := (1 + heatConstant) * varianceConstant ell H β

theorem meanConstant_nonneg {ell H β : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H) :
    0 ≤ meanConstant ell H β := by
  exact mul_nonneg (mul_nonneg hH (GaussianAudit.gaussianAbsMoment_nonneg _))
    (Real.rpow_nonneg (mul_nonneg lowerConstant_pos.le hell) _)

theorem varianceConstant_nonneg {ell H β : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H) :
    0 ≤ varianceConstant ell H β := by
  exact mul_nonneg (mul_nonneg (by positivity) (incrementMoment_nonneg _))
    (Real.rpow_nonneg (mul_nonneg lowerConstant_pos.le hell) _)

theorem memoryConstant_nonneg {ell H β : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H) :
    0 ≤ memoryConstant ell H β := by
  exact mul_nonneg (by linarith [heatConstant_pos]) (varianceConstant_nonneg hell hH)

/-- Both sources of one-input variation in the actual Gaussian update: the
physical mean and the nonlinear heat-square variance. -/
theorem profileUpdate_two_inputs {a : ℝ → ℝ} {φ ψ c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β r : ℝ} (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcl : ∀ s ∈ Ioo 0 r, ∀ y, ell ≤ c (s, y))
    (hcu : ∀ s ∈ Ioo 0 r, ∀ y, c (s, y) ≤ M)
    (hdl : ∀ s ∈ Ioo 0 r, ∀ y, ell ≤ d (s, y))
    (hdu : ∀ s ∈ Ioo 0 r, ∀ y, d (s, y) ≤ M) (x : HeatCircle) :
    |profileUpdate a φ c r x - profileUpdate a ψ d r x| ≤
      (meanConstant ell H β * r ^ ((β - 1) / 4)) * |φ (r, x) - ψ (r, x)| +
      (varianceConstant ell H β * r ^ ((β - 2) / 4)) *
        |varianceMap c r x - varianceMap d r x| := by
  have hvc := varianceMap_elliptic hc hr hr1 hell.le hM hcl hcu x
  have hvd := varianceMap_elliptic hd hr hr1 hell.le hM hdl hdu x
  have hlow : 0 < lowerConstant * ell := mul_pos lowerConstant_pos hell
  have hvc0 : 0 < varianceMap c r x :=
    (mul_pos hlow (Real.rpow_pos_of_pos hr _)).trans_le hvc.1
  have hv := GaussianProfileMean.gaussian_mean_lipschitz_heat_variance_bound
    (varianceMap c r x).toNNReal a ha Ua haB hβ hβ1 hH hlow hr
    (by simpa only [Real.coe_toNNReal _ hvc0.le] using hvc.1)
    hholder (ψ (r, x)) (φ (r, x))
  change |gaussianAverage a (φ (r, x)) (varianceMap c r x) -
    gaussianAverage a (ψ (r, x)) (varianceMap c r x)| ≤
      (meanConstant ell H β * r ^ ((β - 1) / 4)) * |φ (r, x) - ψ (r, x)| at hv
  have hw := gaussianAverage_variance_lipschitz ha haB hH hβ (by linarith : β ≤ 2)
    (mul_pos hlow (Real.rpow_pos_of_pos hr _)) hvc.1 hvd.1 hholder (ψ (r, x))
  have hp : (lowerConstant * ell * r ^ (1 / 2 : ℝ)) ^ (β / 2 - 1) =
      (lowerConstant * ell) ^ (β / 2 - 1) * r ^ ((β - 2) / 4) := by
    rw [Real.mul_rpow hlow.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
    congr 2
    ring
  rw [hp] at hw
  have hw' : |gaussianAverage a (ψ (r, x)) (varianceMap c r x) -
      gaussianAverage a (ψ (r, x)) (varianceMap d r x)| ≤
      (varianceConstant ell H β * r ^ ((β - 2) / 4)) *
        |varianceMap c r x - varianceMap d r x| := by
    simpa only [varianceConstant, mul_assoc] using hw
  exact (abs_sub_le _ (gaussianAverage a (ψ (r, x)) (varianceMap c r x)) _).trans (add_le_add hv hw')

/-- The actual L² profile difference satisfies the manuscript's singular
Volterra inequality. The spatial variance transfer and both Gaussian
Lipschitz estimates are conclusions of earlier proofs. -/
theorem scalar_profile_l2_volterra {a : ℝ → ℝ} {φ ψ c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β r : ℝ} (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hmean : MemLp (fun x => φ (r, x) - ψ (r, x)) 2 haarAddCircle)
    (hcf : ∀ x, c (r, x) = profileUpdate a φ c r x)
    (hdf : ∀ x, d (r, x) = profileUpdate a ψ d r x) :
    normTwo haarAddCircle (fun x => c (r, x) - d (r, x)) ≤
      (meanConstant ell H β * r ^ ((β - 1) / 4)) *
        normTwo haarAddCircle (fun x => φ (r, x) - ψ (r, x)) +
      memoryConstant ell H β * r ^ ((β - 2) / 4) *
        (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) *
          normTwo haarAddCircle (fun y => c (s, y) - d (s, y))) := by
  have hcB : ∀ s ∈ Ioo 0 r, ∀ y, |c (s, y)| ≤ M := by
    intro s _ y
    rw [abs_of_nonneg (hell.le.trans (hcb _).1)]
    exact (hcb _).2
  have hdB : ∀ s ∈ Ioo 0 r, ∀ y, |d (s, y)| ≤ M := by
    intro s _ y
    rw [abs_of_nonneg (hell.le.trans (hdb _).1)]
    exact (hdb _).2
  have ht : MemLp (fun x => c (r, x) - d (r, x)) 2 haarAddCircle := by
    apply bounded_memLp (C := 2 * M) ((hc.sub hd).comp (measurable_const.prodMk measurable_id))
    intro x
    change |c (r, x) - d (r, x)| ≤ 2 * M
    have hcR : |c (r, x)| ≤ M := by
      rw [abs_of_nonneg (hell.le.trans (hcb _).1)]
      exact (hcb _).2
    have hdR : |d (r, x)| ≤ M := by
      rw [abs_of_nonneg (hell.le.trans (hdb _).1)]
      exact (hdb _).2
    exact (abs_sub (c (r, x)) (d (r, x))).trans (by linarith)
  have hV := (varianceMap_memLp hc hr hr1 hM hcB).sub (varianceMap_memLp hd hr hr1 hM hdB)
  have hA : 0 ≤ meanConstant ell H β * r ^ ((β - 1) / 4) :=
    mul_nonneg (meanConstant_nonneg hell.le hH) (Real.rpow_nonneg hr.le _)
  have hB : 0 ≤ varianceConstant ell H β * r ^ ((β - 2) / 4) :=
    mul_nonneg (varianceConstant_nonneg hell.le hH) (Real.rpow_nonneg hr.le _)
  have he := normTwo_sum_bound ht hmean hV hA hB (fun x => by
    rw [hcf x, hdf x]
    exact profileUpdate_two_inputs ha hc hd hell hM hH hβ hβ1 hr hr1 haB hholder
      (fun _ _ _ => (hcb _).1) (fun _ _ _ => (hcb _).2)
      (fun _ _ _ => (hdb _).1) (fun _ _ _ => (hdb _).2) x)
  have htransfer := varianceMap_normTwo_lipschitz hc hd hr hr1 hM hcB hdB
  have hmul := mul_le_mul_of_nonneg_left htransfer hB
  calc
    _ ≤ _ := he
    _ ≤ (meanConstant ell H β * r ^ ((β - 1) / 4)) *
        normTwo haarAddCircle (fun x => φ (r, x) - ψ (r, x)) +
        (varianceConstant ell H β * r ^ ((β - 2) / 4)) *
          ((1 + heatConstant) * (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) *
            normTwo haarAddCircle (fun y => c (s, y) - d (s, y)))) := add_le_add le_rfl hmul
    _ = _ := by unfold memoryConstant; ring

/-- Genuine one-input L² stability for exact bounded measurable scalar
profiles. The only input on the physical means is their actual L² distance;
all covariance transfer, Gaussian regularization, and Volterra absorption
have been proved. -/
theorem scalar_profile_l2_stability {a : ℝ → ℝ} {φ ψ c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β h D : ℝ} (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hD : 0 ≤ D) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hmean : ∀ r ∈ Ioc 0 h, MemLp (fun x => φ (r, x) - ψ (r, x)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => φ (r, x) - ψ (r, x)) ≤ D)
    (hsmall : memoryConstant ell H β * ProfileVolterra.powerConstant ((β - 1) / 4) *
      h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a φ c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a ψ d r x) :
    ∀ r ∈ Ioc 0 h,
      normTwo haarAddCircle (fun x => c (r, x) - d (r, x)) ≤
        2 * (meanConstant ell H β * D) * r ^ ((β - 1) / 4) ∧
      IntervalIntegrable (fun s => (r - s) ^ (-(1 / 2 : ℝ)) *
        normTwo haarAddCircle (fun y => c (s, y) - d (s, y))) volume 0 r ∧
      (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) *
        normTwo haarAddCircle (fun y => c (s, y) - d (s, y))) ≤
        2 * (meanConstant ell H β * D) * ProfileVolterra.powerConstant ((β - 1) / 4) *
          r ^ ((β + 1) / 4) := by
  let f : ℝ → ℝ := fun r => normTwo haarAddCircle (fun x => c (r, x) - d (r, x))
  have hf : Measurable f := spatial_normTwo_measurable (hc.sub hd)
  have hfb : ∀ r ∈ Ioc 0 h, f r ≤ 2 * M := by
    intro r _
    apply normTwo_bound (μ := haarAddCircle)
      ((hc.sub hd).comp (measurable_const.prodMk measurable_id)) (by positivity)
    intro x
    change |c (r, x) - d (r, x)| ≤ 2 * M
    have hcp := hcb (r, x)
    have hdp := hdb (r, x)
    rw [abs_le]
    constructor <;> linarith
  have hvol : ∀ r ∈ Ioc 0 h, f r ≤
      (meanConstant ell H β * D) * r ^ ((β - 1) / 4) +
      memoryConstant ell H β * r ^ ((β - 2) / 4) *
        (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) * f s) := by
    intro r hr
    have he := scalar_profile_l2_volterra ha hc hd hell hM hH hβ.le hβ1 hr.1 (hr.2.trans hh1)
      haB hholder hcb hdb (hmean r hr).1 (hcf r hr) (hdf r hr)
    have hm := mul_le_mul_of_nonneg_left (hmean r hr).2
      (mul_nonneg (meanConstant_nonneg (β := β) hell.le hH) (Real.rpow_nonneg hr.1.le ((β - 1) / 4)))
    calc
      _ ≤ _ := he
      _ ≤ (meanConstant ell H β * r ^ ((β - 1) / 4)) * D +
          memoryConstant ell H β * r ^ ((β - 2) / 4) *
            (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) * f s) := add_le_add hm le_rfl
      _ = _ := by ring
  exact ProfileVolterra.profile_volterra_stability hβ hβ1 hh hh1
    (mul_nonneg (meanConstant_nonneg hell.le hH) hD) (memoryConstant_nonneg hell.le hH)
    (by positivity : 0 ≤ 2 * M) hf (fun _ _ => normTwo_nonneg _ _) hfb hsmall hvol

theorem exists_l2_stability_horizon {ell H β : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H)
    (hβ : 0 < β) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ memoryConstant ell H β *
      ProfileVolterra.powerConstant ((β - 1) / 4) * h ^ (β / 4) ≤ 1 / 2 :=
  ProfileVolterra.exists_absorption_horizon (by linarith)
    (memoryConstant_nonneg hell hH) (by positivity)

end SHE.ProfileStability
