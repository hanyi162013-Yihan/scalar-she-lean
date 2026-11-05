module

public import SHE.GaussianAudit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.GaussianAudit
open Set MeasureTheory StoppedFourier
open scoped InnerProductSpace
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The genuine stopped-history leverage has the sharp negative time
power mass bound whenever its actual reference square energy is bounded.
This form applies to real covariance frames without complexifying them. -/
theorem rpow_historyLeverage_of_energy (z : κ → ι → ℂ) (σ target : ι → ℝ)
    (center : ι → HeatCircle) (hages : ∀ i,σ i ≤ target i) {s α R : ℝ}
    (hs : 0 < s) (hα : -1 < α) (hα0 : α < 0) (hR : 0 ≤ R)
    (hstop : ∀ i,s ≤ σ i)
    (henergy : (∑ k,‖historyTimeVector Finset.univ (z k) σ target center
      (fun i _ => hages i) 0‖^2) ≤ R) :
    Integrable (fun u => u^α*historyLeverage z σ target center u) (volume.restrict (Ici 0)) ∧
      (∫ u in Ici 0,u^α*historyLeverage z σ target center u) ≤
        R*(s/2)^α*(1+2/(α+1)) := by
  have hmass : (∫ u in Ici 0,historyLeverage z σ target center u) ≤ R := by
    rw [integral_historyLeverage_energy z σ target center hages 0]
    exact henergy
  have hearly : ∀ u ∈ Icc (0:ℝ) (0+s/2),historyLeverage z σ target center u ≤ (4/s)*R := by
    intro u hu
    exact (historyLeverage_early_energy_bound z σ target center hages hs
      (fun i => by simpa using hstop i) hu).trans
      (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hs2 : 0 < s/2 := by positivity
  have hi : IntegrableOn (fun u : ℝ => u^α) (Icc 0 (s/2)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' hα (a := 0) (b := s/2)).1
  have he := weighted_density_bound (historyLeverage z σ target center) (fun u : ℝ => u^α)
    hs hR (Real.rpow_nonneg hs2.le α) (historyLeverage_measurable z σ target center hages)
    (historyLeverage_integrable z σ target center hages 0)
    (historyLeverage_nonneg z σ target center) hmass hearly (measurable_id.pow_const α)
    (fun u hu => Real.rpow_nonneg hu α) (by simpa only [zero_add] using hi)
    (fun u hu => Real.rpow_le_rpow_of_nonpos hs2 (by linarith) hα0.le)
  have hn : α+1 ≠ 0 := by linarith
  have hint : (∫ u in Icc (0:ℝ) (s/2),u^α) = (s/2)^(α+1)/(α+1) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hs2.le,
      integral_rpow (Or.inl hα),Real.zero_rpow hn,sub_zero]
  refine ⟨he.1,he.2.trans_eq ?_⟩
  simp only [zero_add,hint]
  rw [Real.rpow_add hs2,Real.rpow_one]
  field_simp
  ring

end SHE.GaussianAudit
