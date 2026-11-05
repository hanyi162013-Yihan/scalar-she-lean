module
public import SHE.NativePairedGammaTrace
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeConvexGammaTrace
open Set MeasureTheory AddCircle Real StoppedFourier FiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

theorem norm_convex_sq {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e:ℝ} (he:0≤e) (he1:e≤1) (x y:E):
    ‖e • x+(1-e) • y‖^2≤e*‖x‖^2+(1-e)*‖y‖^2:=by
  have hbar:0≤1-e:=sub_nonneg.mpr he1
  have hn:‖e • x+(1-e) • y‖≤e*‖x‖+(1-e)*‖y‖:=by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg he,abs_of_nonneg hbar] using norm_add_le (e • x) ((1-e) • y)
  have hs:=pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [mul_nonneg (mul_nonneg he hbar) (sq_nonneg (‖x‖-‖y‖))]

/-- Convex interpolation of the ACTUAL noise columns retains a signed
slot only on the changed endpoint; common additive/frozen terms are
not doubled. No convex Haar factor is invented. -/
theorem combine {I E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a r s:I→E) {e S F:ℝ} (he:0≤e) (he1:e≤1) (hS:0≤S)
    (ha:Summable (fun i=>‖a i‖^2+‖r i‖^2)) (hb:Summable (fun i=>‖a i‖^2+‖s i‖^2))
    (hA:(∑'i,(‖a i‖^2+‖r i‖^2))≤S+F) (hB:(∑'i,(‖a i‖^2+‖s i‖^2))≤F):
    Summable (fun i=>‖a i‖^2+‖e • r i+(1-e) • s i‖^2) ∧
      (∑'i,(‖a i‖^2+‖e • r i+(1-e) • s i‖^2))≤S+F:=by
  have hbar:0≤1-e:=sub_nonneg.mpr he1
  have hp(i:I):‖a i‖^2+‖e • r i+(1-e) • s i‖^2≤
      e*(‖a i‖^2+‖r i‖^2)+(1-e)*(‖a i‖^2+‖s i‖^2):=by
    have hn:=norm_convex_sq he he1 (r i) (s i)
    nlinarith
  have hm:= (ha.mul_left e).add (hb.mul_left (1-e))
  have hs:=Summable.of_nonneg_of_le (fun i=>add_nonneg (sq_nonneg _) (sq_nonneg _)) hp hm
  refine ⟨hs,?_⟩
  have hl:=hs.tsum_le_tsum hp hm
  rw [(ha.mul_left e).tsum_add (hb.mul_left (1-e)),tsum_mul_left,tsum_mul_left] at hl
  have hx:=add_le_add (mul_le_mul_of_nonneg_left hA he) (mul_le_mul_of_nonneg_left hB hbar)
  exact hl.trans (hx.trans (by nlinarith [mul_nonneg hbar hS]))

theorem exists_convex_trace (m U : ℝ) (hm : 0<m) {ρ : ℝ} (hρ : 0<ρ) (hρhalf : ρ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀ (Λ t : ℝ) (hΛ : 1≤Λ) (ht : 0<t) (ht1 : t≤1)
      (κ : ℝ) (hκ : 0<κ) (b : Fin 6→CircleL2) (B : ℝ) (hB : 0≤B)
      (hb : ∀ i,∀ᵐ x∂haarAddCircle,‖b i x‖≤B) (c0 c1 r0 r1 : EllipticField m U) (e:ℝ) (he:0≤e) (he1:e≤1),
    let col:=fun (i : Fin 6) (f : CircleHeat.CircleL2) (q : HaarNode)=>
      OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (NativeMultiplierTrace.multiplier (b i) B (hb i) (circleHeatOperator t ht.le
          (CircleNormalization.push (globalHaarColumn q f))))
    let additive:=fun q=>col 0 (AdditiveHaarForcing.constantField κ hκ).1 q-
      col 3 (AdditiveHaarForcing.constantField κ hκ).1 q-
      col 2 (AdditiveHaarForcing.constantField κ hκ).1 q+col 5 (AdditiveHaarForcing.constantField κ hκ).1 q
    let residual1:=fun q=>col 0 c0.1 q-col 3 r0.1 q-col 2 c1.1 q+col 5 r1.1 q
    let residual0:=fun q=>col 0 c0.1 q-col 3 r0.1 q-col 2 c0.1 q+col 5 r1.1 q
    let residual:=fun q=>e • residual1 q+(1-e) • residual0 q
    Summable (fun q=>‖additive q‖^2+‖residual q‖^2) ∧
      (∑' q,(‖additive q‖^2+‖residual q‖^2))≤6*(
        C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hΛ hρ.le c1 c0+
        HaarWeightedHeat.higherConstant m U hm 0 ρ*B^2*(NativeHeatSpan.clock t)^(ρ-1/2)*‖r0.1-r1.1‖^2+
        (κ+U)*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*
          (‖b 0-b 1‖^2+‖b 1-b 2‖^2+‖b 3-b 4‖^2+‖b 4-b 5‖^2)) := by
  obtain ⟨C,hC,hold⟩:=NativePairedGammaTrace.exists_paired_trace m U hm hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro Λ t hΛ ht ht1 κ hκ b B hB hb c0 c1 r0 r1 e he he1 col additive residual1 residual0 residual
  have ha:=hold Λ t hΛ ht ht1 κ hκ b B hB hb c0 c1 r0 r1
  have hz:=hold Λ t hΛ ht ht1 κ hκ b B hB hb c0 c0 r0 r1
  let S0:=C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hΛ hρ.le c1 c0
  let F0:=HaarWeightedHeat.higherConstant m U hm 0 ρ*B^2*(NativeHeatSpan.clock t)^(ρ-1/2)*‖r0.1-r1.1‖^2+
    (κ+U)*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*
      (‖b 0-b 1‖^2+‖b 1-b 2‖^2+‖b 3-b 4‖^2+‖b 4-b 5‖^2)
  have hS:0≤6*S0:=by
    dsimp only [S0,NativeSignedHaarProcess.inputEnergy,NativeHeatSpan.clock]
    positivity
  have hA:(∑'q,(‖additive q‖^2+‖residual1 q‖^2))≤6*S0+6*F0:=by
    convert! ha.2 using 1 <;> dsimp only [S0,F0] <;> ring
  have hB0:(∑'q,(‖additive q‖^2+‖residual0 q‖^2))≤6*F0:=by
    simpa only [NativeSignedHaarProcess.inputEnergy,sub_self,map_zero,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0),mul_zero,zero_add] using hz.2
  have hc:=combine additive residual1 residual0 he he1 hS ha.1 hz.1 hA hB0
  refine ⟨hc.1,hc.2.trans_eq ?_⟩
  dsimp only [S0,F0]
  ring

end SHE.NativeConvexGammaTrace
