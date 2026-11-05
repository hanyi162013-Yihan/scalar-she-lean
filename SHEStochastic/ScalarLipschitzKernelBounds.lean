module

public import SHEStochastic.ScalarLipschitzHeatColumns
public import SHEStochastic.NativeFourierStateSeparation
public import SHEStochastic.HolderCoefficientContinuity
public import SHEStochastic.StateNoiseCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzKernelBounds
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzHeatColumn ScalarLipschitzHeatColumns
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "w" => NativeFourierHeatCoordinate.weight
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {I : Type*} (e : HilbertBasis I ℝ Noise)

theorem weighted_sub (a b : Noise) (k : C(HeatCircle,ℝ)) :
    weighted (a-b) k=weighted a k-weighted b k := by
  apply Lp.ext
  filter_upwards [weighted_ae (a-b) k,weighted_ae a k,weighted_ae b k,
    Lp.coeFn_sub (weighted a k) (weighted b k),Lp.coeFn_sub a b] with x hc ha hb hd he
  rw [hc,hd,he]
  change k x*(a x-b x)=weighted a k x-weighted b k x
  rw [ha,hb]
  exact mul_sub _ _ _

theorem kernel_sub (r : ℝ) (a b : Noise) : kernel e r (a-b)=kernel e r a-kernel e r b := by
  by_cases hr : 0<r
  · apply lp.ext
    funext i
    change column r (a-b) (e i)=column r a (e i)-column r b (e i)
    apply NativeFourierStateSeparation.ext <;> intro n
    all_goals rw [map_sub,column_mode hr,column_mode hr,column_mode hr,weighted_sub,inner_sub_left,mul_sub]
  · simp only [kernel_zero e (le_of_not_gt hr),sub_zero]

theorem kernel_measurable [Countable I] :
    @Measurable (ℝ×Noise) (HilbertColumns.Space I RealL2) _ (borel _)
      (fun p => kernel e p.1 p.2) :=
  HilbertColumns.measurable_of_columns (fun i => column_measurable (e i))

def coefficient {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g) (u : RealL2) : Noise :=
  HolderCoefficientIntegrability.coefficient zero_lt_one le_rfl hg (NativePhysicalState.push u)

theorem coefficient_norm_difference {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
    (u v : RealL2) : ‖coefficient hg u-coefficient hg v‖≤(C : ℝ)*‖u-v‖ := by
  simpa only [coefficient,NNReal.coe_one,Real.rpow_one,←map_sub,LinearIsometry.norm_map] using
    HolderCoefficientContinuity.difference_norm ν zero_lt_one le_rfl hg
      (NativePhysicalState.push u) (NativePhysicalState.push v)

theorem coefficient_continuous {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g) :
    Continuous (coefficient hg) :=
  (HolderCoefficientContinuity.continuous ν zero_lt_one le_rfl hg).comp NativePhysicalState.push.continuous

theorem weighted_coefficient {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
    (u : RealL2) (k : C(HeatCircle,ℝ)) :
    weighted (coefficient hg u) k=StateNoiseCovariance.row ν zero_lt_one le_rfl hg k
      (NativePhysicalState.push u) := rfl

def heatConstant (H : ℝ) : ℝ := H^(1/2 : ℝ)+2*HeatTrace.fractionalGaussianIntegral 0

theorem heatConstant_nonneg {H : ℝ} (hH : 0≤H) : 0≤heatConstant H :=
  add_nonneg (Real.rpow_nonneg hH _) (mul_nonneg (by norm_num)
    (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ)<1/2)).le)

theorem trace_bound {H r : ℝ} (hr : 0<r) (hRH : r≤H) :
    (∑' n : ℤ,Real.exp (-r*(n : ℝ)^2))≤heatConstant H*r^(-(1/2 : ℝ)) := by
  have h := (ScalarHeatFourierEnergy.trace (show 0<r/2 by positivity)).2
  rw [show 2*(r/2)=r by ring] at h
  refine h.trans ?_
  unfold heatConstant
  rw [add_mul,Real.rpow_neg hr.le]
  have hpow : r^(1/2 : ℝ)≤H^(1/2 : ℝ) :=
    Real.rpow_le_rpow hr.le hRH (by norm_num)
  have hrp : 0<r^(1/2 : ℝ) := Real.rpow_pos_of_pos hr _
  have hdiv : 1≤H^(1/2 : ℝ)*(r^(1/2 : ℝ))⁻¹ := by
    rw [←div_eq_mul_inv,one_le_div hrp]
    exact hpow
  exact add_le_add hdiv le_rfl

theorem kernel_bound {H r : ℝ} (hr : 0<r) (hRH : r≤H) (a : Noise) :
    ‖kernel e r a‖^2≤heatConstant H*r^(-(1/2 : ℝ))*‖a‖^2 := by
  have he (n : ℤ) : (Real.exp (-r*(n : ℝ)^2))^2≤Real.exp (-r*(n : ℝ)^2) := by
    rw [pow_two,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hr.le (sq_nonneg (n : ℝ))]
  have hs : Summable (fun n : ℤ => Real.exp (-r*(n : ℝ)^2)) := by
    simpa only [show 2*(r/2)=r by ring] using (ScalarHeatFourierEnergy.trace (show 0<r/2 by positivity)).1
  rw [kernel_norm_sq e hr]
  exact mul_le_mul_of_nonneg_right
    (((damp_summable hr).tsum_le_tsum he hs).trans (trace_bound hr hRH)) (sq_nonneg _)

private theorem gain {x : ℝ} (hx : 0≤x) :
    1-Real.exp (-x)≤x^(1/8 : ℝ) := by
  by_cases h : x≤1
  · exact (by linarith [Real.add_one_le_exp (-x)] : 1-Real.exp (-x)≤x).trans
      (Real.self_le_rpow_of_le_one hx h (by norm_num))
  · exact (by linarith [Real.exp_pos (-x)] : 1-Real.exp (-x)≤1).trans
      (Real.one_le_rpow (le_of_not_ge h) (by norm_num))

private theorem rpow_exp_bound {x : ℝ} (hx : 0≤x) :
    x^(1/4 : ℝ)*Real.exp (-x)≤1 := by
  have hp : x^(1/4 : ℝ)≤Real.exp x := by
    by_cases h : x≤1
    · exact (Real.rpow_le_one hx h (by norm_num)).trans (Real.one_le_exp hx)
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge h) (by norm_num)).trans (by
        linarith [Real.add_one_le_exp x])
  calc
    _ ≤ Real.exp x*Real.exp (-x) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = 1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]

/-- Old-noise time increment for the true Fourier heat multiplier.
The quarter power of the time difference leaves an integrable age
exponent of three quarters. -/
theorem increment_bound {H r δ : ℝ} (hr : 0<r) (hRH : r≤H) (hδ : 0≤δ) (a : Noise) :
    ‖kernel e (r+δ) a-kernel e r a‖^2≤
      heatConstant H*δ^(1/4 : ℝ)*r^(-(3/4 : ℝ))*‖a‖^2 := by
  let d (n : ℤ) := Real.exp (-(r+δ)*(n : ℝ)^2)-Real.exp (-r*(n : ℝ)^2)
  let K := δ^(1/4 : ℝ)*r^(-(1/4 : ℝ))
  have he (n : ℤ) : (d n)^2≤K*Real.exp (-r*(n : ℝ)^2) := by
    let q := (n : ℝ)^2
    have hq : 0≤q := sq_nonneg _
    have hδq : 0≤δ*q := mul_nonneg hδ hq
    have hrq : 0≤r*q := mul_nonneg hr.le hq
    have h₁ : 0≤1-Real.exp (-(δ*q)) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hδq))
    have h₂ := pow_le_pow_left₀ h₁ (gain hδq) 2
    have hd : d n=-(1-Real.exp (-(δ*q)))*Real.exp (-(r*q)) := by
      unfold d
      change Real.exp (-(r+δ)*q)-Real.exp (-r*q)=_
      rw [show -(r+δ)*q=-(δ*q)+ -(r*q) by ring,Real.exp_add,neg_mul]
      ring
    have h₃ : (δ*q)^(1/4 : ℝ)=K*(r*q)^(1/4 : ℝ) := by
      dsimp only [K]
      rw [Real.mul_rpow hδ hq,Real.mul_rpow hr.le hq,Real.rpow_neg hr.le]
      have hh := Real.rpow_pos_of_pos hr (1/4 : ℝ)
      calc
        _ = δ^(1/4 : ℝ)*q^(1/4 : ℝ) := rfl
        _ = δ^(1/4 : ℝ)*((r^(1/4 : ℝ))⁻¹*r^(1/4 : ℝ))*q^(1/4 : ℝ) := by
          rw [inv_mul_cancel₀ hh.ne',mul_one]
        _ = _ := by ring
    rw [hd,mul_pow,neg_sq]
    calc
      _ ≤ ((δ*q)^(1/8 : ℝ))^2*(Real.exp (-(r*q)))^2 :=
        mul_le_mul_of_nonneg_right h₂ (sq_nonneg _)
      _ = K*((r*q)^(1/4 : ℝ)*Real.exp (-(r*q)))*Real.exp (-(r*q)) := by
        rw [←Real.rpow_mul_natCast hδq]
        norm_num only [Nat.cast_ofNat,show (1/8 : ℝ)*2=1/4 by norm_num]
        rw [h₃]
        ring
      _ ≤ K*Real.exp (-r*(n : ℝ)^2) := by
        have hK : 0≤K := mul_nonneg (Real.rpow_nonneg hδ _) (Real.rpow_nonneg hr.le _)
        simpa only [mul_one,neg_mul] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (rpow_exp_bound hrq) hK) (Real.exp_pos (-(r*q))).le
  have hs : Summable (fun n : ℤ => Real.exp (-r*(n : ℝ)^2)) := by
    simpa only [show 2*(r/2)=r by ring] using (ScalarHeatFourierEnergy.trace (show 0<r/2 by positivity)).1
  have hd : Summable (fun n : ℤ => (d n)^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) he (hs.mul_left K)
  rw [HilbertColumns.norm_sq]
  have hX (i : I) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
      φ ψ n ((kernel e (r+δ) a-kernel e r a) i)=d n*inner ℝ (weighted a (w ψ n)) (e i) := by
    change φ ψ n (column (r+δ) a (e i)-column r a (e i))=_
    rw [map_sub,column_mode (add_pos_of_pos_of_nonneg hr hδ),column_mode hr]
    exact (sub_mul _ _ _).symm
  rw [(spectral_energy e a d hd _ hX).2]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ ∑' n : ℤ,K*Real.exp (-r*(n : ℝ)^2) := hd.tsum_le_tsum he (hs.mul_left K)
    _ ≤ K*(heatConstant H*r^(-(1/2 : ℝ))) := by
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (trace_bound hr hRH) (by dsimp only [K]; positivity)
    _ = _ := by
      dsimp only [K]
      calc
        _ = heatConstant H*δ^(1/4 : ℝ)*(r^(-(1/4 : ℝ))*r^(-(1/2 : ℝ))) := by ring
        _ = _ := by rw [←Real.rpow_add hr]; norm_num

end SHEStochastic.ScalarLipschitzKernelBounds
