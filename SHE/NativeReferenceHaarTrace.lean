module

public import SHE.HaarWeightedTaylor
public import SHE.NativeMultiplierTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeReferenceHaarTrace
open Set Finset MeasureTheory AddCircle Real StoppedFourier FiniteHaar DyadicApproximation HaarWeightedHeat
open scoped ENNReal
local instance nativeReferenceHaarTrace_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeReferenceHaarTrace_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- Genuine j=0 specialization of the proved all-order matched trace.
It supplies the extra positive-time output gain for the changed frozen
profile factor, using its actual L2 coefficient difference. -/
theorem unit_trace {Λ ρ t : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (f g : RealL2) (m U : ℝ) (hm : 0<m)
    (hf : ∀ᵐ y∂haarAddCircle,m≤(realEmbed f y).re ∧ (realEmbed f y).re≤U)
    (hg : ∀ᵐ y∂haarAddCircle,m≤(realEmbed g y).re ∧ (realEmbed g y).re≤U)
    (b : CircleHeat.CircleL2) (B : ℝ) (hB : 0≤B) (hb : ∀ᵐ y∂haarAddCircle,‖b y‖≤B) :
    Summable (fun q : HaarNode=>‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (globalHaarColumn q (realEmbed g)-globalHaarColumn q (realEmbed f))‖^2) ∧
    (∑' q : HaarNode,‖weightedHeat Λ ρ t hΛ hρ.le b B hb
      (globalHaarColumn q (realEmbed g)-globalHaarColumn q (realEmbed f))‖^2)≤
      higherConstant m U hm 0 ρ*B^2*t^(ρ-1/2)*‖realEmbed (g-f)‖^2 := by
  have hU:=elliptic_upper_nonneg (realEmbed f) m U hm hf
  have he : realEmbed f+realEmbed (g-f)=realEmbed g := by rw [map_sub];abel
  have hbound : ∀ᵐ y∂haarAddCircle,‖realEmbed (g-f) y‖≤2*U := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (realEmbed g) (realEmbed f),
      CircleMultiplier.elliptic_norm_bound _ m U hm (realEmbed_real f) hf,
      CircleMultiplier.elliptic_norm_bound _ m U hm (realEmbed_real g) hg] with y hy hfy hgy
    rw [hy]
    exact (norm_sub_le _ _).trans (by linarith)
  have hR (q : HaarNode) : globalColumnTaylorRemainder q (realEmbed f) (realEmbed (g-f)) 0=
      globalHaarColumn q (realEmbed g)-globalHaarColumn q (realEmbed f) := by
    simp only [globalColumnTaylorRemainder,he,zero_add,range_one,sum_singleton,Nat.factorial_zero,
      Nat.cast_one,inv_one,iteratedFDeriv_zero_apply,one_smul]
  have hh:=global_taylor_weighted_heat hΛ hρ hρhalf ht ht1 f (g-f) m U (2*U) hm (by positivity)
    hf (by rw [he];exact hg) hbound 0 b B hB hb
  simpa only [hR,Nat.factorial_zero,Nat.cast_one,inv_one,one_pow,one_mul,mul_zero,pow_zero,mul_one] using hh

/-- Literal native Q M_b S_tau(L_d-L_c), with the TRUE output-age
rho gain and the actual spatial L2 profile difference. Native clock
normalization is explicit. Arbitrary dependence of b,c,d is allowed. -/
theorem trace {Λ ρ t m U : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hm : 0<m)
    (b : StoppedFourier.CircleL2) (B : ℝ) (hB : 0≤B) (hb : ∀ᵐ x∂haarAddCircle,‖b x‖≤B)
    (c d : EllipticField m U) :
    let col:=fun q : HaarNode=>OneInputOperator.besselHalf Λ ρ hΛ hρ.le
      (NativeMultiplierTrace.multiplier b B hb (circleHeatOperator t ht.le
        (CircleNormalization.push (globalHaarColumn q d.1-globalHaarColumn q c.1))))
    Summable (fun q=>‖col q‖^2) ∧
      (∑' q,‖col q‖^2)≤higherConstant m U hm 0 ρ*B^2*
        (NativeHeatSpan.clock t)^(ρ-1/2)*‖d.1-c.1‖^2 := by
  intro col
  have hct:=NativeHeatSpan.clock_pos ht
  have hct1 : NativeHeatSpan.clock t≤1 := by
    apply (div_le_one (by positivity : (0:ℝ)<4*π^2)).mpr
    exact ht1.trans (by nlinarith [Real.two_le_pi])
  let hb':=CircleNormalization.push_symm_ae_property b (fun z=>‖z‖≤B) hb
  have hh:=unit_trace hΛ hρ hρhalf hct hct1
    (NativeSignedHaarProcess.realCoefficient c) (NativeSignedHaarProcess.realCoefficient d) m U hm
    (by simpa only [NativeSignedHaarProcess.realEmbed_realCoefficient] using c.2.2)
    (by simpa only [NativeSignedHaarProcess.realEmbed_realCoefficient] using d.2.2)
    (CircleNormalization.push.symm b) B hB hb'
  have he (q : HaarNode) : ‖col q‖^2=
      ‖weightedHeat Λ ρ (NativeHeatSpan.clock t) hΛ hρ.le (CircleNormalization.push.symm b) B hb'
        (globalHaarColumn q d.1-globalHaarColumn q c.1)‖^2 := by
    dsimp only [col]
    rw [NativeMultiplierTrace.multiplier_heat_push b B hb ht.le]
    change _=‖CircleNormalization.push.symm (OneInputOperator.besselHalf Λ ρ hΛ hρ.le (CircleNormalization.push _))‖^2
    rw [CircleNormalization.push.symm.norm_map]
    rfl
  simpa only [he,map_sub,NativeSignedHaarProcess.realEmbed_realCoefficient] using hh

end SHE.NativeReferenceHaarTrace
