module

public import SHE.JointInsertionBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointInsertionIntegrability
open Set MeasureTheory StoppedFourier WordRecursion CovarianceEndpoint GaussianItoTest
open PhysicalRemainderBound PhysicalRemainderMass UniformSmooth CutoffWordLevel JointWordAnalytic
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (Λ : ℝ)
variable {U V : Ω×ℝ→CircleL2} {XU XV : Ω×(ℝ×HeatCircle)→ℝ}
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
include hU hV hXU hXV

/-- The actual local insertion admits the spatial and temporal Fubini
operations for arbitrary old joint observations. -/
theorem time_integrable (p : P) (ω : Ω) :
    IntervalIntegrable (fun t => ∫ x : HeatCircle,insertion L Λ U V XU XV p ω t x ∂AddCircle.haarAddCircle)
      volume R.base (L.terminal p) := by
  have hmap : Measurable (fun z : ℝ×HeatCircle => (((p,ω),z.1),z.2)) :=
    ((measurable_const (a := (p,ω))).prodMk measurable_fst).prodMk measurable_snd
  have hm := (insertion_measurable L Λ hU hV hXU hXV).comp hmap
  have ht := hm.stronglyMeasurable.integral_prod_right' (ν := AddCircle.haarAddCircle)
  obtain ⟨A,hAn,hA⟩ := (UniformBoundedSmooth.fixed (P := Unit) R.totalVariance_smooth).norm_bound
  obtain ⟨C,hCn,hC⟩ := L.test_uniform.norm_bound
  obtain ⟨D,hDn,hD⟩ := L.test_uniform.fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := L.test_uniform.fderiv.fderiv.norm_bound
  let K : ℝ := (1/2:ℝ)*(A+R.upper)*B*n
  have hd : IntervalIntegrable (fun t => K*(1+heatConstant*(L.terminal p-t)^(-(1/2:ℝ))))
      volume R.base (L.terminal p) := endpoint_majorant_integrable K
  apply hd.mono_fun' ht.aestronglyMeasurable
  rw [uIoc_of_le (L.terminal_base p)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (L.terminal p))] with t htin hne
  have hW : t∈Ioo (L.window p).left (L.window p).right := ⟨htin.1,lt_of_le_of_ne htin.2 hne⟩
  exact JointInsertionBounds.spatial_bound (L.window p) hAn
    (fun z => by simpa only [Real.norm_eq_abs] using hA () z) hBn (fun tx => XV (ω,tx)) hW
    (backward (L.window p) (L.test p) t) (state L Λ U V XU XV p ω t)
    (BackwardRegularity.gaussian_state_hessian_bound _ ((L.test_uniform.smooth p).of_le (by simp))
      (hC p) (hD p) (hB p) _)

end SHE.JointInsertionIntegrability
