module
public import SHE.OldIntervalVariance

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.StoppedRowSquareMass
open Set MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures
  StoppedFourier WordRecursion ProfileVariance
local instance stoppedRowSquareMass_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {n:ℕ}

/-- Every literal stopped row coordinate has its genuine spatial L²
mass, bounded at the common insertion gap even for unequal targets. -/
theorem coordinate_bound (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hages:∀i,σ i≤target i){lo hi:ℝ}(hgap:lo<hi)(hgap1:hi-lo≤1)
    (hstop:∀i,σ i≤lo ∨ hi≤σ i)(i:Fin n):
    Integrable (fun x:HeatCircle=>stoppedRow σ target center (lo,x) i^2) haarAddCircle ∧
      (∫x:HeatCircle,stoppedRow σ target center (lo,x) i^2 ∂haarAddCircle)≤
        (1+heatConstant)*(hi-lo)^(-(1/2:ℝ)):=by
  rcases hstop i with hinactive|hactive
  · have he:(fun x:HeatCircle=>stoppedRow σ target center (lo,x) i^2)=fun _=>0:=by
      funext x
      simp only [stoppedRow,PiLp.toLp_apply,ite_eq_right (not_lt.mpr hinactive),zero_pow (by norm_num:2≠0)]
    rw [he]
    refine ⟨integrable_const (0:ℝ),?_⟩
    simp only [integral_zero]
    exact mul_nonneg (by linarith [heatConstant_pos]) (Real.rpow_nonneg (sub_pos.mpr hgap).le _)
  · have hage:0<target i-lo:=by linarith [hages i]
    have he:(fun x:HeatCircle=>stoppedRow σ target center (lo,x) i^2)=
        fun x=>‖heatPhysical (target i-lo) (center i) x‖^2:=by
      funext x
      simp only [stoppedRow,PiLp.toLp_apply,ite_eq_left (hgap.trans_le hactive)]
      rw [←heatPhysical_real hage]
      simp only [Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [he]
    refine ⟨heatPhysical_square_integrable hage _,?_⟩
    rw [heatPhysical_square_mass hage]
    have hb:=circleHeat_norm_sq_bound hage (center i)
    have hp:(target i-lo)^(-(1/2:ℝ))≤(hi-lo)^(-(1/2:ℝ)):=
      Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hgap) (by linarith [hages i]) (by norm_num)
    have hone:1≤(hi-lo)^(-(1/2:ℝ)):=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.mpr hgap) hgap1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hp heatConstant_pos.le]

end SHE.StoppedRowSquareMass
