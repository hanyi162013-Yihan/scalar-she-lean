module

public import SHE.HilbertColumns
public import SHE.NegativeThreeLeg

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace SHE.SquareSeriesField
open MeasureTheory
open scoped NNReal ENNReal
variable {P I : Type*} [MeasurableSpace P] [Countable I]

theorem good_measurable (v : P→I→ℂ) (hv : ∀ i,Measurable (fun p=>v p i)) :
    MeasurableSet {p|Summable (fun i=>‖v p i‖^2)} := by
  have hm : Measurable (fun p=>∑' i : I,((‖v p i‖₊^2:ℝ≥0):ℝ≥0∞)):=
    Measurable.tsum (fun i=>((hv i).nnnorm.pow_const 2).coe_nnreal_ennreal)
  have he (p : P) : (∑' i : I,((‖v p i‖₊^2:ℝ≥0):ℝ≥0∞))≠⊤ ↔
      Summable (fun i=>‖v p i‖^2) := by
    have hh:=ENNReal.tsum_coe_ne_top_iff_summable_coe (f:=fun i=>‖v p i‖₊^2)
    have hr : (fun i=>((‖v p i‖₊^2:ℝ≥0):ℝ))=(fun i=>‖v p i‖^2) := by
      funext i
      rw [NNReal.coe_pow,coe_nnnorm]
    rw [hr] at hh
    exact hh
  have hs:=(measurableSet_eq_fun hm (measurable_const : Measurable (fun _ : P=>(⊤:ℝ≥0∞)))).compl
  convert! hs using 1
  ext p
  exact (he p).symm

def value (v : P→I→ℂ) (p : P) : HilbertColumns.Space I ℂ := by
  classical
  exact if h : Summable (fun i=>‖v p i‖^2) then HilbertColumns.ofSummable (v p) h else 0

theorem value_apply (v : P→I→ℂ) (p : P) (h : Summable (fun i=>‖v p i‖^2)) (i : I) :
    value v p i=v p i := by simp only [value,dif_pos h,HilbertColumns.ofSummable]

theorem value_norm_sq (v : P→I→ℂ) (p : P) : ‖value v p‖^2=∑' i,‖v p i‖^2 := by
  classical
  by_cases h : Summable (fun i=>‖v p i‖^2)
  · rw [HilbertColumns.norm_sq]
    exact tsum_congr (fun i=>by rw [value_apply v p h i])
  · simp only [value,dif_neg h,norm_zero,zero_pow (by decide : (2:ℕ)≠0),tsum_eq_zero_of_not_summable h]

theorem value_measurable (v : P→I→ℂ) (hv : ∀ i,Measurable (fun p=>v p i)) :
    @Measurable P (HilbertColumns.Space I ℂ) _ (borel _) (value v) := by
  classical
  apply HilbertColumns.measurable_of_columns
  intro i
  have he : (fun p=>value v p i)=fun p=>if h : Summable (fun j=>‖v p j‖^2) then v p i else 0 := by
    funext p
    by_cases h : Summable (fun j=>‖v p j‖^2)
    · simp only [dif_pos h,value_apply v p h i]
    · simp only [value,dif_neg h,lp.coeFn_zero,Pi.zero_apply]
  rw [he]
  exact (hv i).ite (good_measurable v hv) measurable_const

end SHE.SquareSeriesField

namespace SHE.NativeNegativeRealization
open MeasureTheory StoppedFourier
local instance nativeNegativeRealization_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeNegativeRealization_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeNegativeRealization_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeNegativeRealization_lpSigma : MeasurableSpace (HilbertColumns.Space ℤ ℂ):=borel _
local instance nativeNegativeRealization_lpBorel : BorelSpace (HilbertColumns.Space ℤ ℂ):=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

def coefficients (mass ρ : ℝ) (g : P×HeatCircle→ℂ) (p : P) (n : ℤ) : ℂ:=
  (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x=>g (p,x)) n

def value (mass ρ : ℝ) (g : P×HeatCircle→ℂ) (p : P) : CircleL2:=
  (fourierBasis (T:=2*Real.pi)).repr.symm (SquareSeriesField.value (coefficients mass ρ g) p)

theorem value_measurable (mass ρ : ℝ) (g : P×HeatCircle→ℂ) (hg : Measurable g) :
    Measurable (value mass ρ g) := by
  have hc : ∀ n,Measurable (fun p=>coefficients mass ρ g p n):=fun n=>
    measurable_const.mul (NativeFourierAverage.scalar_coefficient_measurable g hg n)
  exact (fourierBasis (T:=2*Real.pi)).repr.symm.continuous.measurable.comp
    (SquareSeriesField.value_measurable (coefficients mass ρ g) hc)

theorem coefficients_norm_sq (mass ρ : ℝ) (hmass : 1≤mass)
    (g : P×HeatCircle→ℂ) (p : P) (n : ℤ) :
    ‖coefficients mass ρ g p n‖^2=(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x=>g (p,x)) n‖^2 := by
  have hb : 0≤mass+(n:ℝ)^2:=by nlinarith [sq_nonneg (n:ℝ)]
  rw [coefficients,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hb _),←Real.rpow_mul_natCast hb]
  norm_num only [Nat.cast_ofNat]
  rw [show (-ρ/2)*(2:ℝ) = -ρ by ring]

theorem value_norm_sq (mass ρ : ℝ) (hmass : 1≤mass) (g : P×HeatCircle→ℂ) (p : P) :
    ‖value mass ρ g p‖^2=NativeFourierAverage.scalarEnergy mass ρ (fun x=>g (p,x)) := by
  rw [value,LinearIsometryEquiv.norm_map,SquareSeriesField.value_norm_sq]
  exact tsum_congr (fun n=>coefficients_norm_sq mass ρ hmass g p n)

theorem value_fourier (mass ρ : ℝ) (hmass : 1≤mass) (g : P×HeatCircle→ℂ) (p : P)
    (hs : Summable (fun n : ℤ=>(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x=>g (p,x)) n‖^2)) (n : ℤ) :
    fourierCoeff (value mass ρ g p) n=coefficients mass ρ g p n := by
  have hh : Summable (fun n : ℤ=>‖coefficients mass ρ g p n‖^2):=
    hs.congr (fun n=>(coefficients_norm_sq mass ρ hmass g p n).symm)
  rw [←fourierBasis_repr]
  change ((fourierBasis (T:=2*Real.pi)).repr
    ((fourierBasis (T:=2*Real.pi)).repr.symm _)) n=_
  rw [LinearIsometryEquiv.apply_symm_apply,SquareSeriesField.value_apply _ p hh n]

end SHE.NativeNegativeRealization
