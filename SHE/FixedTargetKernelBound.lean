module

public import SHE.PastReferenceBracket
public import SHE.HaarIntegrandEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.FixedTargetKernelBound
open MeasureTheory Set FiniteHaar HaarIntegrandEnergy NativeHeatObservation
open scoped NNReal

def constant (M : ℝ) : ℝ := singleConstant M/timeScale^(-(1/2:ℝ))

theorem constant_nonneg {M : ℝ} (hM : 0≤M) : 0≤constant M :=
  div_nonneg (singleConstant_nonneg hM) (Real.rpow_nonneg timeScale_pos.le _)

theorem timeScale_one_le : 1≤timeScale := by
  unfold timeScale
  nlinarith [Real.one_le_pi_div_two]

/-- The actual native Hilbert column has a deterministic inverse-root
bound, with the physical clock factor retained in the constant. -/
theorem kernel_bound {ell M t : ℝ} (hell : 0<ell) (ht : 0<t) (ht1 : t≤1)
    (f : EllipticField ell M) :
    ‖NativeHeatObservation.kernel ell M hell (t,f)‖^2≤constant M*t^(-(1/2:ℝ)) := by
  have hclock : t/timeScale≤1 := (div_le_one timeScale_pos).2 (ht1.trans timeScale_one_le)
  have hb := kernel_small_bound hell (div_pos ht timeScale_pos) hclock f
  change ‖NativeHeatObservation.kernel ell M hell (t,f)‖^2≤singleConstant M*(t/timeScale)^(-(1/2:ℝ)) at hb
  rw [Real.div_rpow ht.le timeScale_pos.le] at hb
  exact hb.trans_eq (by unfold constant; ring)

/-- Both reference profiles remain bounded, so the stopped full-target
signed noise has a deterministic inverse-root cap. This estimate is
used only to construct its continuous version; the sharper D_v-dependent
reference bracket remains available separately. -/
theorem raw_bound {Ω : Type*} (P : CanonicalCovariance.ProfileParameters)
    (Λ κ θ η : ℝ) (hκ : κ<P.lower) (v b : ℝ≥0) (hspan : (b:ℝ)-(v:ℝ)≤1)
    (data : Ω → ControlledProfile.Inputs) (r : ℝ≥0) (hrb : r≤b) (ω : Ω) :
    ‖PastReferenceBracket.raw P Λ κ θ η hκ v b data (r,ω)‖^2≤
      (4*constant (P.upper-κ))*((b:ℝ)-(r:ℝ))^(-(1/2:ℝ)) := by
  have hM : 0≤P.upper-κ := by have := P.lower_bound 0; have := P.upper_bound 0; linarith
  have hC := constant_nonneg hM
  by_cases hr : r∈Ioc v b
  · rw [PastReferenceBracket.raw,indicator_of_mem (show (r,ω)∈Ioc v b ×ˢ (univ:Set Ω) from ⟨hr,mem_univ _⟩)]
    rcases lt_or_eq_of_le hr.2 with hlt | rfl
    · have hage : 0<(b:ℝ)-(r:ℝ) := sub_pos.mpr (by exact_mod_cast hlt)
      have hage1 : (b:ℝ)-(r:ℝ)≤1 := by have := NNReal.coe_lt_coe.mpr hr.1; linarith
      have hu := kernel_bound (sub_pos.mpr hκ) hage hage1
        (FrozenReferenceFields.field P Λ κ θ hκ v data (r,ω))
      have hv := kernel_bound (sub_pos.mpr hκ) hage hage1
        (FrozenReferenceFields.field P Λ κ η hκ v data (r,ω))
      exact ((pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans
        (add_pow_le (norm_nonneg _) (norm_nonneg _) 2)).trans (by norm_num only at *; nlinarith)
    · simp only [sub_self,NativeHeatObservation.kernel_zero _ le_rfl,
        sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Real.zero_rpow (by norm_num : -(1/2:ℝ)≠0),mul_zero,le_refl]
  · rw [PastReferenceBracket.raw,indicator_of_notMem (show (r,ω)∉Ioc v b ×ˢ (univ:Set Ω) from fun hh => hr hh.1)]
    simp only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hrb)) _)

end SHE.FixedTargetKernelBound
