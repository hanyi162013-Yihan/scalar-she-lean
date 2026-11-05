module

public import SHE.GaussianMeanHolder
public import SHE.HolderNormTwo

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ProfileHolderL2
open Set MeasureTheory AddCircle StoppedFourier ProfileVariance GaussianProfile ProfileL2 ProfileStability
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- The actual scalar profile Volterra inequality with Holder mean input,
so no negative time power is charged to the physical displacement. -/
theorem volterra {a : ℝ → ℝ} {φ ψ c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β r : ℝ} (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hmean : MemLp (fun x => φ (r, x) - ψ (r, x)) 2 haarAddCircle)
    (hcf : ∀ x, c (r, x) = profileUpdate a φ c r x)
    (hdf : ∀ x, d (r, x) = profileUpdate a ψ d r x) :
    normTwo haarAddCircle (fun x => c (r, x) - d (r, x)) ≤
      H * (normTwo haarAddCircle (fun x => φ (r, x) - ψ (r, x)))^β +
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
  have hpow:=HolderNormTwo.power hmean hβ hβ1
  have hA : 0≤H:=hH
  have hB : 0 ≤ varianceConstant ell H β * r ^ ((β - 2) / 4) :=
    mul_nonneg (varianceConstant_nonneg hell.le hH) (Real.rpow_nonneg hr.le _)
  have he := normTwo_sum_bound ht hpow.1 hV hA hB (fun x => by
    rw [hcf x, hdf x]
    simpa only [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (φ (r,x)-ψ (r,x))) β),Pi.sub_apply] using
      GaussianMeanHolder.update_two_inputs (φ:=φ) (ψ:=ψ) ha hc hd hell hM hH hβ hβ1 hr hr1 haB hholder
      (fun _ _ _ => (hcb _).1) (fun _ _ _ => (hcb _).2)
      (fun _ _ _ => (hdb _).1) (fun _ _ _ => (hdb _).2) x)
  have htransfer := varianceMap_normTwo_lipschitz hc hd hr hr1 hM hcB hdB
  have hmul := mul_le_mul_of_nonneg_left htransfer hB
  calc
    _ ≤ _ := he
    _ ≤ H * (normTwo haarAddCircle (fun x => φ (r, x) - ψ (r, x)))^β +
        (varianceConstant ell H β * r ^ ((β - 2) / 4)) *
          ((1 + heatConstant) * (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) *
            normTwo haarAddCircle (fun y => c (s, y) - d (s, y)))) := add_le_add (mul_le_mul_of_nonneg_left hpow.2 hH) hmul
    _ = _ := by unfold memoryConstant; ring


/-- Exact bounded measurable profiles inherit the Holder L2 input modulus
on a fixed small horizon, independent of the particular physical means. -/
theorem stability {a : ℝ → ℝ} {φ ψ c d : ℝ × HeatCircle → ℝ}
    {ell M Ua H β h D : ℝ} (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (hell : 0 < ell) (hM : 0 ≤ M) (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hD : 0 ≤ D) (haB : ∀ z, |a z| ≤ Ua)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hmean : ∀ r ∈ Ioc 0 h, MemLp (fun x => φ (r, x) - ψ (r, x)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x => φ (r, x) - ψ (r, x)) ≤ D)
    (hsmall : 6 * memoryConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a φ c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a ψ d r x) :
    ∀ r ∈ Ioc 0 h,
      normTwo haarAddCircle (fun x => c (r, x) - d (r, x)) ≤ 2*(H*D^β) := by
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
      H*D^β +
      memoryConstant ell H β * r ^ ((β - 2) / 4) *
        (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) * f s) := by
    intro r hr
    have he := volterra ha hc hd hell hM hH hβ.le hβ1 hr.1 (hr.2.trans hh1)
      haB hholder hcb hdb (hmean r hr).1 (hcf r hr) (hdf r hr)
    have hm := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (normTwo_nonneg _ _) (hmean r hr).2 hβ.le) hH
    calc
      _ ≤ _ := he
      _ ≤ H*D^β +
          memoryConstant ell H β * r ^ ((β - 2) / 4) *
            (∫ s in (0 : ℝ)..r, (r - s) ^ (-(1 / 2 : ℝ)) * f s) := add_le_add hm le_rfl
      _ = _ := by ring
  exact ProfileVolterra.profile_holder_volterra_stability hβ hh hh1
    (mul_nonneg hH (Real.rpow_nonneg hD _)) (memoryConstant_nonneg hell.le hH)
    (by positivity : 0≤2*M) hf (fun _ _=>normTwo_nonneg _ _) hfb hsmall hvol

end SHE.ProfileHolderL2
