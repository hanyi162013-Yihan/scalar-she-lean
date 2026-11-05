module

public import SHE.GapSimplexMassBound
public import SHE.RootConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.RootPowerGapKernels
open Set MeasureTheory Real GapSimplexFaces
open scoped BigOperators

def kernel (ν p : ℝ) (root : Bool) (t : ℝ) : ℝ := if root then rootKernel ν t else t^(p-1)

def mass (ν p : ℝ) (root : Bool) (w : ℝ) : ℝ := if root then rootMass ν w else w^p/p

theorem kernel_measurable (ν p : ℝ) (root : Bool) : Measurable (kernel ν p root) := by
  cases root
  · exact real_rpow_measurable _
  · exact rootKernel_measurable ν

theorem kernel_nonneg {ν : ℝ} (hν : 0≤ν) (p : ℝ) (root : Bool) {t : ℝ} (ht : 0<t) :
    0≤kernel ν p root t := by
  cases root
  · exact Real.rpow_nonneg ht.le _
  · exact rootKernel_nonneg hν ht.le

theorem mass_nonneg {ν w p : ℝ} (hν : 0≤ν) (hw : 0≤w) (hp : 0≤p) (root : Bool) :
    0≤mass ν p root w := by
  cases root
  · exact div_nonneg (Real.rpow_nonneg hw _) hp
  · exact rootMass_nonneg hν hw

theorem cut_integrable_of_interval {w : ℝ} (hw : 0≤w) (f : ℝ→ℝ)
    (hi : IntervalIntegrable f volume 0 w) : Integrable (cut w f) := by
  have hh : IntegrableOn f (Ioo 0 w) := by
    rw [←integrableOn_Ioc_iff_integrableOn_Ioo]
    simpa only [uIoc_of_le hw] using hi.def'
  convert! (integrable_indicator_iff measurableSet_Ioo).mpr hh using 1
  funext t
  simp only [cut,indicator_apply]

theorem cut_integral_eq_interval {w : ℝ} (hw : 0≤w) (f : ℝ→ℝ) :
    (∫ t,cut w f t)=∫ t in (0:ℝ)..w,f t := by
  have he : cut w f=(Ioo 0 w).indicator f := by
    funext t
    simp only [cut,indicator_apply]
  rw [he]
  rw [integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
    ←intervalIntegral.integral_of_le hw]

theorem kernel_cut_integrable {ν w p : ℝ} (hν : 0≤ν) (hw : 0≤w) (hp : 0<p) (root : Bool) :
    Integrable (cut w (kernel ν p root)) := by
  apply cut_integrable_of_interval hw
  cases root
  · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  · exact rootKernel_intervalIntegrable hν hw

theorem kernel_cut_integral {ν w p : ℝ} (hν : 0≤ν) (hw : 0≤w) (hp : 0<p) (root : Bool) :
    (∫ t,cut w (kernel ν p root) t)=mass ν p root w := by
  rw [cut_integral_eq_interval hw]
  cases root
  · change (∫ t in (0:ℝ)..w,t^(p-1))=w^p/p
    rw [integral_rpow (Or.inl (by linarith)),show p-1+1=p by ring,
      Real.zero_rpow hp.ne',sub_zero]
  · rfl

theorem inverse_cap {N w t : ℝ} (hN : 0<N) (hw : 0<w) (ht : w/N≤t) :
    t⁻¹≤N/w := by
  have hh := one_div_le_one_div_of_le (div_pos hw hN) ht
  have he : 1/(w/N)=N/w := by field_simp
  simpa only [one_div,he] using hh

theorem kernel_mass_cap {ν N w p t : ℝ} (hν : 0≤ν) (hN : 0<N) (hw : 0<w)
    (hp : 0<p) (hp1 : p≤1) (ht : w/N≤t) (htw : t≤w) (root : Bool) :
    kernel ν p root t≤N/w*mass ν p root w := by
  have ht0 : 0<t := (div_pos hw hN).trans_le ht
  have hn : 0≤N/w := div_nonneg hN.le hw.le
  have hinv := inverse_cap hN hw ht
  cases root
  · change t^(p-1)≤N/w*(w^p/p)
    have he : t^(p-1)=t⁻¹*t^p := by
      rw [←Real.rpow_neg_one,←Real.rpow_add ht0]
      congr 1
      ring
    have hmass : w^p≤w^p/p := by
      apply (le_div_iff₀ hp).mpr
      exact mul_le_of_le_one_right (Real.rpow_nonneg hw.le _) hp1
    rw [he]
    exact (mul_le_mul hinv (Real.rpow_le_rpow ht0.le htw hp.le)
      (Real.rpow_nonneg ht0.le _) hn).trans (mul_le_mul_of_nonneg_left hmass hn)
  · change rootKernel ν t≤N/w*rootMass ν w
    have hc : min 1 (ν*t^(1/4:ℝ))≤min 1 (ν*w^(1/4:ℝ)) := by
      exact min_le_min_left _ (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ht0.le htw (by norm_num)) hν)
    have hc0 : 0≤min 1 (ν*t^(1/4:ℝ)) :=
      le_min (by norm_num) (mul_nonneg hν (Real.rpow_nonneg ht0.le _))
    unfold rootKernel
    rw [Real.rpow_neg_one]
    exact (mul_le_mul hinv hc hc0 hn).trans
      (mul_le_mul_of_nonneg_left (root_clip_le_mass hν hw.le) hn)

/-- Actual mixed root/power gap integrals retain the exact root masses.
Every positive degree is attached to its original gap. -/
theorem simplex_integral_bound {k : ℕ} {ν w : ℝ} (hν : 0≤ν) (hw : 0<w)
    (p : Fin (k+1)→ℝ) (hp : ∀ i,0<p i) (hp1 : ∀ i,p i≤1)
    (root : Fin (k+1)→Bool) :
    Integrable (GapSimplexFaces.density w (fun i=>kernel ν (p i) (root i))) ∧
      (∫ d,GapSimplexFaces.density w (fun i=>kernel ν (p i) (root i)) d)≤
        ((k+1:ℕ):ℝ)^2/w*(∏ i,mass ν (p i) (root i) w) := by
  exact density_mass_bound hw _ (fun i=>kernel_measurable ν (p i) (root i))
    (fun i t ht=>kernel_nonneg hν (p i) (root i) ht)
    (fun i=>kernel_cut_integrable hν hw.le (hp i) (root i))
    (fun i=>mass ν (p i) (root i) w)
    (fun i=>mass_nonneg hν hw.le (hp i).le (root i))
    (fun i=>kernel_cut_integral hν hw.le (hp i) (root i))
    (fun i t ht htw=>kernel_mass_cap hν (by positivity) hw (hp i) (hp1 i) ht htw (root i))

end SHE.RootPowerGapKernels
