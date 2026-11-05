module

public import SHE.CompactMollifier
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ScaledMollifierKernel
open Set MeasureTheory Real SmoothConvolution
open scoped ContDiff

def unitKernel : ℝ→ℝ:=CompactMollifier.kernel 1 (by norm_num)
def kernel (r : ℝ) (x : ℝ) : ℝ:=r⁻¹*unitKernel (r⁻¹*x)

theorem unit_smooth : ContDiff ℝ ∞ unitKernel:=CompactMollifier.kernel_smooth 1 (by norm_num)
theorem unit_compact : HasCompactSupport unitKernel:=CompactMollifier.kernel_compact 1 (by norm_num)
theorem unit_mass : (∫ x,unitKernel x)=1:=CompactMollifier.kernel_mass 1 (by norm_num)
theorem unit_nonneg (x : ℝ) : 0≤unitKernel x:=CompactMollifier.kernel_nonneg 1 (by norm_num) x

theorem kernel_smooth (r : ℝ) : ContDiff ℝ ∞ (kernel r) := by
  change ContDiff ℝ ∞ (fun x=>r⁻¹*unitKernel (r⁻¹*x))
  exact contDiff_const.mul (unit_smooth.comp (contDiff_const.mul contDiff_id))

theorem kernel_compact {r : ℝ} (hr : 0<r) : HasCompactSupport (kernel r) := by
  have hc : HasCompactSupport (fun x : ℝ=>unitKernel (r⁻¹*x)) := by
    simpa only [smul_eq_mul] using unit_compact.comp_smul (inv_ne_zero hr.ne')
  convert! (hc.mul_left (f:=fun _ : ℝ=>r⁻¹)) using 1

theorem kernel_integrable {r : ℝ} (hr : 0<r) : Integrable (kernel r) :=
  (kernel_smooth r).continuous.integrable_of_hasCompactSupport (kernel_compact hr)

theorem kernel_nonneg {r : ℝ} (hr : 0≤r) (x : ℝ) : 0≤kernel r x :=
  mul_nonneg (inv_nonneg.mpr hr) (unit_nonneg _)

theorem kernel_mass {r : ℝ} (hr : 0<r) : (∫ x,kernel r x)=1 := by
  change (∫ x,r⁻¹*unitKernel (r⁻¹*x))=1
  rw [integral_const_mul,Measure.integral_comp_mul_left]
  simp only [inv_inv,abs_of_pos hr,smul_eq_mul,unit_mass,mul_one,inv_mul_cancel₀ hr.ne']

/-- Exact all-order scaling of one fixed actual smooth kernel. -/
theorem kernel_jet (r : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (kernel r) x=(r⁻¹)^(n+1)*iteratedDeriv n unitKernel (r⁻¹*x) := by
  change iteratedDeriv n (fun y=>r⁻¹*unitKernel (r⁻¹*y)) x=_
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (unit_smooth.of_le (by simp)) r⁻¹]
  simp only [pow_succ]
  ring

/-- The L1 norm of each derivative scales by exactly r^(-n), with
one fixed finite kernel constant per derivative order. -/
theorem kernel_jet_l1 {r : ℝ} (hr : 0<r) (n : ℕ) :
    (∫ x,‖iteratedDeriv n (kernel r) x‖)=(r⁻¹)^n*(∫ x,‖iteratedDeriv n unitKernel x‖) := by
  simp_rw [kernel_jet,norm_mul,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) (n+1))]
  rw [integral_const_mul,Measure.integral_comp_mul_left (fun y=>‖iteratedDeriv n unitKernel y‖) r⁻¹]
  simp only [inv_inv,abs_of_pos hr,smul_eq_mul,pow_succ]
  have he : r⁻¹*r=1:=inv_mul_cancel₀ hr.ne'
  calc
    _=(r⁻¹)^n*((r⁻¹*r)*(∫ x,‖iteratedDeriv n unitKernel x‖)):=by ring
    _=_:=by rw [he,one_mul]

theorem unit_tsupport : tsupport unitKernel⊆Icc (-1:ℝ) 1 := by
  rw [unitKernel,CompactMollifier.kernel,(CompactMollifier.bump 1 (by norm_num)).tsupport_normed_eq]
  intro x hx
  have hh : |x|≤1:=by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,CompactMollifier.bump] using hx
  exact abs_le.mp hh

theorem kernel_tsupport {r : ℝ} (hr : 0<r) : tsupport (kernel r)⊆Icc (-r) r := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  have hne : unitKernel (r⁻¹*x)≠0:=by
    intro h
    exact hx (by simp only [kernel,h,mul_zero])
  have hb:=unit_tsupport (subset_tsupport _ hne)
  have ha : |r⁻¹*x|≤1:=abs_le.mpr hb
  rw [abs_mul,abs_inv,abs_of_pos hr] at ha
  have hm:=mul_le_mul_of_nonneg_left ha hr.le
  rw [←mul_assoc,mul_inv_cancel₀ hr.ne',one_mul,mul_one] at hm
  exact abs_le.mp hm

end SHE.ScaledMollifierKernel
