module

public import SHE.NativeMultiplierTrace
public import SHE.RawKernelColumns
public import SHE.HilbertTrace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeOutputTrace
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
  NativeMultiplierTrace OneInputOperator
open scoped ENNReal
local instance nativeOutputTrace_periodPositive : Fact (0<2*π) := ⟨by positivity⟩

/-- Exact heat action on the full physical Fourier basis. -/
theorem heat_basis (t : ℝ) (ht : 0≤t) (l : ℤ) :
    circleHeatOperator t ht (fourierBasis (T:=2*π) l)=
      (exp (-t*(l:ℝ)^2):ℂ) • fourierBasis (T:=2*π) l := by
  apply (fourierBasis (T:=2*π)).repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr,circleHeatOperator_fourierCoeff]
  rw [fourierCoeff_congr_ae (Lp.coeFn_smul (exp (-t*(l:ℝ)^2):ℂ) (fourierBasis (T:=2*π) l)),
    fourierCoeff.const_smul]
  simp_rw [←fourierBasis_repr,HilbertBasis.repr_self]
  by_cases hn : n=l
  · subst n
    simp
  · simp [lp.single_apply,hn,Ne.symm hn]

theorem multiplier_basis (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B) (l : ℤ) :
    multiplier b B hb (fourierBasis (T:=2*π) l)=modulate l b := by
  apply Lp.ext
  have hbasis : (fourierBasis (T:=2*π) l : HeatCircle→ℂ)=ᵐ[haarAddCircle] fourier l := by
    simpa only [coe_fourierBasis] using coeFn_fourierLp (T:=2*π) 2 l
  filter_upwards [multiplier_ae b B hb (fourierBasis (T:=2*π) l),
    (modulation_memLp b l).coeFn_toLp,hbasis] with x hm hp he
  change modulate l b x=fourier l x*b x at hp
  rw [hm,hp,he]
  exact mul_comm _ _

/-- The existing two-time one-input operator columns are EXACTLY the
literal bounded multiplier/heat composition, not a surrogate operator. -/
theorem column_eq_literal {Λ ρ t s : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ)
    (ht : 0≤t) (hs : 0≤s) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B) (l : ℤ) :
    besselHalf Λ ρ hΛ hρ (circleHeatOperator t ht
      (multiplier b B hb (circleHeatOperator s hs (fourierBasis (T:=2*π) l))))=
      column Λ ρ t s hΛ hρ ht b l := by
  rw [heat_basis s hs l,map_smul,multiplier_basis,map_smul,map_smul]
  rfl

/-- Full actual Fourier-basis trace of Q S_t M_b S_s. The multiplier
uses its spatial L2 norm; the coarse bound only defines its operator. -/
theorem two_time_trace {Λ ρ t s : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2)
    (ht : 0≤t) (hs : 0≤s) (hage : 0<t+s) (hsmall : t+s≤1)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B) :
    let A := (besselHalf Λ ρ hΛ hρ).comp
      ((circleHeatOperator t ht).comp ((multiplier b B hb).comp (circleHeatOperator s hs)))
    Summable (fun l : ℤ=>‖A (fourierBasis (T:=2*π) l)‖^2) ∧
      (∑' l : ℤ,‖A (fourierBasis (T:=2*π) l)‖^2)≤
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t+s)^(ρ-1/2))*‖b‖^2 := by
  intro A
  have he (l : ℤ) : A (fourierBasis (T:=2*π) l)=column Λ ρ t s hΛ hρ ht b l :=
    column_eq_literal hΛ hρ ht hs b B hb l
  simpa only [he] using one_input_trace hΛ hρ hρhalf ht hs hage hsmall b

/-- The output multiplier trace used by the complete actual martingale,
with an arbitrary dependent bounded right factor applied pathwise. -/
theorem output_right_trace {G I : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {Λ ρ s : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hs : 0<s) (hs1 : s≤1)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B)
    (R : G→L[ℂ] CircleL2) (g : HilbertBasis I ℂ G) :
    let A := (besselHalf Λ ρ hΛ hρ).comp ((multiplier b B hb).comp (circleHeatOperator s hs.le))
    Summable (fun i=>‖(A.comp R) (g i)‖^2) ∧
      (∑' i,‖(A.comp R) (g i)‖^2)≤
        ‖R‖^2*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*s^(ρ-1/2))*‖b‖^2 := by
  intro A
  have hzero := two_time_trace hΛ hρ hρhalf (by norm_num : (0:ℝ)≤0) hs.le
    (by simpa using hs) (by simpa using hs1) b B hb
  have hh : Summable (fun l : ℤ=>‖A (fourierBasis (T:=2*π) l)‖^2) ∧
      (∑' l : ℤ,‖A (fourierBasis (T:=2*π) l)‖^2)≤
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*s^(ρ-1/2))*‖b‖^2 := by
    simpa only [A,ContinuousLinearMap.comp_apply,SignedKernelColumns.native_heat_zero,zero_add] using hzero
  have hright := HilbertTrace.right_comp A R (fourierBasis (T:=2*π)) (fourierBasis (T:=2*π)) g hh.1
  exact ⟨hright.1,(hright.2.trans (mul_le_mul_of_nonneg_left hh.2 (sq_nonneg _))).trans_eq (by ring)⟩

end SHE.NativeOutputTrace
