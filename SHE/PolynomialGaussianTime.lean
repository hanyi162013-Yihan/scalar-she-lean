module

public import SHE.AnnularTime
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.PolynomialGaussianTime
open Set MeasureTheory Real

def kernel (γ s L t : ℝ) : ℝ:=t^(γ-1)*min 1 ((L*t)^(-s))

theorem unit_head {γ s : ℝ} (hs : 0≤s) {t : ℝ} (ht : t∈Ioc (0:ℝ) 1) :
    kernel γ s 1 t=t^(γ-1) := by
  have hp : 1≤t^(-s):=by
    simpa only [one_rpow] using Real.rpow_le_rpow_of_nonpos ht.1 ht.2 (neg_nonpos.mpr hs)
  simp only [kernel,one_mul,min_eq_left hp,mul_one]

theorem unit_tail {γ s : ℝ} (hs : 0≤s) {t : ℝ} (ht : t∈Ioi (1:ℝ)) :
    kernel γ s 1 t=t^(γ-s-1) := by
  have hp : t^(-s)≤1:=by
    simpa only [one_rpow] using Real.rpow_le_rpow_of_nonpos zero_lt_one ht.le (neg_nonpos.mpr hs)
  simp only [kernel,one_mul,min_eq_right hp]
  rw [←Real.rpow_add (zero_lt_one.trans ht)]
  congr 1
  ring

theorem unit_integrable {γ s : ℝ} (hγ : 0<γ) (hs : γ<s) :
    IntegrableOn (kernel γ s 1) (Ioi 0) := by
  have hh : IntegrableOn (kernel γ s 1) (Ioc (0:ℝ) 1):=by
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<γ-1))).congr_fun
      (fun t ht=>(unit_head (hγ.le.trans hs.le) ht).symm) measurableSet_Ioc
  have ht : IntegrableOn (kernel γ s 1) (Ioi (1:ℝ)):=by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : γ-s-1 < -1) zero_lt_one).congr_fun
      (fun t ht=>(unit_tail (hγ.le.trans hs.le) ht).symm) measurableSet_Ioi
  have hu : Ioc (0:ℝ) 1∪Ioi 1=Ioi 0:=by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · exact zero_lt_one.trans h
    · intro h
      by_cases ht : t≤1
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr (lt_of_not_ge ht)
  rw [←hu]
  exact hh.union ht

/-- Exact finite polynomial-decay mass. The exponent s need only
exceed the physical time exponent gamma; exponential annular support is
unnecessary for this time ledger. -/
theorem unit_integral {γ s : ℝ} (hγ : 0<γ) (hs : γ<s) :
    (∫ t in Ioi (0:ℝ),kernel γ s 1 t)=1/γ+1/(s-γ) := by
  have hi:=unit_integrable hγ hs
  have hu : Ioc (0:ℝ) 1∪Ioi 1=Ioi 0:=by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · exact zero_lt_one.trans h
    · intro h
      by_cases ht : t≤1
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr (lt_of_not_ge ht)
  have hd : Disjoint (Ioc (0:ℝ) 1) (Ioi 1):=by
    rw [disjoint_left]
    intro t ht hs
    exact (not_lt_of_ge ht.2) hs
  rw [←hu,setIntegral_union hd measurableSet_Ioi
    (hi.mono_set (by intro t ht; exact ht.1))
    (hi.mono_set (by intro t ht; exact zero_lt_one.trans ht))]
  have hh : (∫ t in Ioc (0:ℝ) 1,kernel γ s 1 t)=1/γ:=by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht=>unit_head (hγ.le.trans hs.le) ht)]
    rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      integral_rpow (Or.inl (by linarith : -1<γ-1)),show γ-1+1=γ by ring,
      Real.one_rpow,Real.zero_rpow hγ.ne',sub_zero]
  have ht : (∫ t in Ioi (1:ℝ),kernel γ s 1 t)=1/(s-γ):=by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht=>unit_tail (hγ.le.trans hs.le) ht),
      integral_Ioi_rpow_of_lt (by linarith : γ-s-1 < -1) zero_lt_one,Real.one_rpow]
    rw [show γ-s-1+1=γ-s by ring]
    field_simp [sub_ne_zero.mpr hs.ne,sub_ne_zero.mpr hs.ne']
    ring
  rw [hh,ht]

theorem scale_eq {γ s L t : ℝ} (hL : 0<L) (ht : 0≤t) :
    kernel γ s L t=L^(1-γ)*kernel γ s 1 (L*t) := by
  have hp : (L*t)^(γ-1)=L^(γ-1)*t^(γ-1):=Real.mul_rpow hL.le ht
  simp only [kernel,one_mul,hp]
  have he : L^(1-γ)*L^(γ-1)=1:=by
    rw [←Real.rpow_add hL,show 1-γ+(γ-1)=0 by ring,Real.rpow_zero]
  calc
    _=(L^(1-γ)*L^(γ-1))*(t^(γ-1)*min 1 ((L*t)^(-s))):=by rw [he,one_mul]
    _=_:=by ring

theorem integrable {γ s L : ℝ} (hγ : 0<γ) (hs : γ<s) (hL : 0<L) :
    IntegrableOn (kernel γ s L) (Ioi 0):=by
  have hh := (integrableOn_Ioi_comp_mul_left_iff (kernel γ s 1) (0:ℝ) hL).2
    (by simpa only [mul_zero] using unit_integrable hγ hs)
  have hg : IntegrableOn (fun t=>L^(1-γ)*kernel γ s 1 (L*t)) (Ioi 0):=hh.const_mul (L^(1-γ))
  apply hg.congr_fun
    (fun t ht=>(scale_eq hL ht.le).symm) measurableSet_Ioi

/-- The exact scaled mass exposes the full L^(-gamma) gain for
polynomial Gaussian cancellation, with a constant independent of scale. -/
theorem integral {γ s L : ℝ} (hγ : 0<γ) (hs : γ<s) (hL : 0<L) :
    (∫ t in Ioi (0:ℝ),kernel γ s L t)=(1/γ+1/(s-γ))*L^(-γ):=by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht=>scale_eq hL ht.le),integral_const_mul,
    integral_comp_mul_left_Ioi (kernel γ s 1) (0:ℝ) hL,mul_zero,unit_integral hγ hs]
  simp only [smul_eq_mul]
  have he : L^(1-γ)*L⁻¹=L^(-γ):=by
    rw [←Real.rpow_neg_one,←Real.rpow_add hL]
    congr 1
    ring
  calc
    _=(1/γ+1/(s-γ))*(L^(1-γ)*L⁻¹):=by ring
    _=_:=by rw [he]

/-- Polynomial heat-band smoothing has EXACTLY the same sharp squared
state-frequency exponent as annular exponential smoothing. -/
theorem frequency_mass {β ρ ν : ℝ} (hβ : β≤1) (hρ0 : -(1/2:ℝ)<ρ) (hρ1 : ρ<1/2) (hν : 0<ν) :
    (∫ t in Ioi (0:ℝ),ν^(2-2*β)*kernel (ρ+1/2) ((3-β)/2) (ν^4) t)=
      (1/(ρ+1/2)+1/(1-β/2-ρ))*ν^(-2*β-4*ρ) := by
  rw [integral_const_mul,integral (by linarith : 0<ρ+1/2)
    (by linarith : ρ+1/2<(3-β)/2) (pow_pos hν 4)]
  rw [←Real.rpow_natCast_mul hν.le]
  have he : (3-β)/2-(ρ+1/2)=1-β/2-ρ:=by ring
  rw [he]
  calc
    _=(1/(ρ+1/2)+1/(1-β/2-ρ))*(ν^(2-2*β)*ν^((4:ℝ)*(-(ρ+1/2)))):=by ring
    _=_:=by rw [←Real.rpow_add hν]; congr 2; ring

end SHE.PolynomialGaussianTime
