module

public import SHE.NativeReferenceHaarTrace
public import SHE.NativeOutputTrace
public import SHE.ScalarHeatGammaSlots
public import SHE.AdditiveHaarForcing

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace SHE.NativePairedGammaTrace
open Set MeasureTheory AddCircle Real StoppedFourier FiniteHaar
open scoped ENNReal BigOperators
local instance nativePairedGammaTrace_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativePairedGammaTrace_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

theorem multiplier_sub (b c : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x∂haarAddCircle,‖b x‖≤B) (hc : ∀ᵐ x∂haarAddCircle,‖c x‖≤B)
    (hd : ∀ᵐ x∂haarAddCircle,‖(b-c) x‖≤2*B) (f : CircleL2) :
    NativeMultiplierTrace.multiplier b B hb f-NativeMultiplierTrace.multiplier c B hc f=
      NativeMultiplierTrace.multiplier (b-c) (2*B) hd f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub b c,Lp.coeFn_sub
    (NativeMultiplierTrace.multiplier b B hb f) (NativeMultiplierTrace.multiplier c B hc f),
    NativeMultiplierTrace.multiplier_ae b B hb f,NativeMultiplierTrace.multiplier_ae c B hc f,
    NativeMultiplierTrace.multiplier_ae (b-c) (2*B) hd f] with x hbc hs h0 h1 h2
  rw [hs,Pi.sub_apply,h0,h1,h2,hbc,Pi.sub_apply]
  ring

theorem ordinary_trace {Λ ρ t m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hm : 0<m) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x∂haarAddCircle,‖b x‖≤B) (c : EllipticField m U) :
    let col:=fun q : HaarNode=>OneInputOperator.besselHalf Λ ρ hΛ hρ
      (NativeMultiplierTrace.multiplier b B hb (circleHeatOperator t ht.le
        (CircleNormalization.push (globalHaarColumn q c.1))))
    Summable (fun q=>‖col q‖^2) ∧
      (∑' q,‖col q‖^2)≤U*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*‖b‖^2 := by
  intro col
  have hh:=NativeOutputTrace.output_right_trace hΛ hρ hρhalf ht ht1 b B hb
    (NativeHaarKernel.factor m U hm c) NativeHaarKernel.inputBasis
  simp only [ContinuousLinearMap.comp_apply,NativeHaarKernel.factor_basis] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right (NativeHaarKernel.factor_norm_sq_le m U hm c)
  exact mul_nonneg (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf]) (rpow_nonneg ht.le _)

/-- A single native paired complete-Gamma trace keeps all six physical
slots. The four displacement/variance multipliers use their TRUE L2
norms. The two changed factors keep respectively the negative-input
energy and the positive rho output-age gain. -/
theorem exists_paired_trace (m U : ℝ) (hm : 0<m) {ρ : ℝ} (hρ : 0<ρ) (hρhalf : ρ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀ (Λ t : ℝ) (hΛ : 1≤Λ) (ht : 0<t) (ht1 : t≤1)
      (κ : ℝ) (hκ : 0<κ) (b : Fin 6→CircleL2) (B : ℝ) (hB : 0≤B)
      (hb : ∀ i,∀ᵐ x∂haarAddCircle,‖b i x‖≤B) (c0 c1 r0 r1 : EllipticField m U),
    let col:=fun (i : Fin 6) (f : CircleHeat.CircleL2) (q : HaarNode)=>
      OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (NativeMultiplierTrace.multiplier (b i) B (hb i) (circleHeatOperator t ht.le
          (CircleNormalization.push (globalHaarColumn q f))))
    let additive:=fun q=>col 0 (AdditiveHaarForcing.constantField κ hκ).1 q-
      col 3 (AdditiveHaarForcing.constantField κ hκ).1 q-
      col 2 (AdditiveHaarForcing.constantField κ hκ).1 q+col 5 (AdditiveHaarForcing.constantField κ hκ).1 q
    let residual:=fun q=>col 0 c0.1 q-col 3 r0.1 q-col 2 c1.1 q+col 5 r1.1 q
    Summable (fun q=>‖additive q‖^2+‖residual q‖^2) ∧
      (∑' q,(‖additive q‖^2+‖residual q‖^2))≤6*(
        C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hΛ hρ.le c1 c0+
        HaarWeightedHeat.higherConstant m U hm 0 ρ*B^2*(NativeHeatSpan.clock t)^(ρ-1/2)*‖r0.1-r1.1‖^2+
        (κ+U)*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*
          (‖b 0-b 1‖^2+‖b 1-b 2‖^2+‖b 3-b 4‖^2+‖b 4-b 5‖^2)) := by
  obtain ⟨C,hC,hsigned⟩:=NativeMultiplierTrace.exists_signed_multiplier_trace m U hm hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro Λ t hΛ ht ht1 κ hκ b B hB hb c0 c1 r0 r1 col additive residual
  let T:=(1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2)
  have hd (i j : Fin 6) : ∀ᵐ x∂haarAddCircle,‖(b i-b j) x‖≤2*B := by
    filter_upwards [hb i,hb j,Lp.coeFn_sub (b i) (b j)] with x hi hj hx
    rw [hx]
    exact (norm_sub_le _ _).trans (by linarith)
  let diff:=fun (i j : Fin 6) (f : CircleHeat.CircleL2) (q : HaarNode)=>col i f q-col j f q
  have de (i j : Fin 6) (f : CircleHeat.CircleL2) (q : HaarNode) : diff i j f q=
      OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (NativeMultiplierTrace.multiplier (b i-b j) (2*B) (hd i j)
          (circleHeatOperator t ht.le (CircleNormalization.push (globalHaarColumn q f)))) := by
    dsimp only [diff,col]
    rw [←map_sub,multiplier_sub (b i) (b j) B (hb i) (hb j) (hd i j)]
  have od (i j : Fin 6) {l W : ℝ} (hl : 0<l) (f : EllipticField l W) :
      Summable (fun q=>‖diff i j f.1 q‖^2) ∧
        (∑' q,‖diff i j f.1 q‖^2)≤W*T*‖b i-b j‖^2 := by
    simpa only [de,T] using ordinary_trace hΛ hρ.le hρhalf ht ht1 hl (b i-b j) (2*B) (hd i j) f
  let v : Fin 6→HaarNode→CircleL2:=fun i=>![
    (fun q=>col 0 c0.1 q-col 0 c1.1 q),diff 0 1 c1.1,diff 1 2 c1.1,
    (fun q=>-(col 3 r0.1 q-col 3 r1.1 q)),(fun q=>-diff 3 4 r1.1 q),(fun q=>-diff 4 5 r1.1 q)] i
  let w : Fin 6→HaarNode→CircleL2:=fun i=>![
    (fun _=>0),diff 0 1 (AdditiveHaarForcing.constantField κ hκ).1,
    diff 1 2 (AdditiveHaarForcing.constantField κ hκ).1,(fun _=>0),
    (fun q=>-diff 3 4 (AdditiveHaarForcing.constantField κ hκ).1 q),
    (fun q=>-diff 4 5 (AdditiveHaarForcing.constantField κ hκ).1 q)] i
  let R0:=C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hΛ hρ.le c1 c0
  let R3:=HaarWeightedHeat.higherConstant m U hm 0 ρ*B^2*(NativeHeatSpan.clock t)^(ρ-1/2)*‖r0.1-r1.1‖^2
  have hs0 : Summable (fun q=>‖v 0 q‖^2) ∧ (∑' q,‖v 0 q‖^2)≤R0 := by
    have hh:=hsigned Λ t hΛ ht ht1 (b 0) B hB (hb 0) c1 c0
    simpa [v,col,R0,map_sub] using hh
  have hs3 : Summable (fun q=>‖v 3 q‖^2) ∧ (∑' q,‖v 3 q‖^2)≤R3 := by
    have hh:=NativeReferenceHaarTrace.trace hΛ hρ hρhalf ht ht1 hm (b 3) B hB (hb 3) r1 r0
    have hh' : Summable (fun q=>‖col 3 r0.1 q-col 3 r1.1 q‖^2) ∧
        (∑' q,‖col 3 r0.1 q-col 3 r1.1 q‖^2)≤R3 := by
      simpa only [col,R3,map_sub] using hh
    change Summable (fun q=>‖-(col 3 r0.1 q-col 3 r1.1 q)‖^2) ∧
      (∑' q,‖-(col 3 r0.1 q-col 3 r1.1 q)‖^2)≤R3
    simpa only [norm_neg] using hh'
  have hv (i : Fin 6) : Summable (fun q=>‖v i q‖^2) := by
    fin_cases i
    · exact hs0.1
    · exact (od 0 1 hm c1).1
    · exact (od 1 2 hm c1).1
    · exact hs3.1
    · simpa [v,norm_neg] using (od 3 4 hm r1).1
    · simpa [v,norm_neg] using (od 4 5 hm r1).1
  have hw (i : Fin 6) : Summable (fun q=>‖w i q‖^2) := by
    fin_cases i
    · simp [w]
    · exact (od 0 1 hκ (AdditiveHaarForcing.constantField κ hκ)).1
    · exact (od 1 2 hκ (AdditiveHaarForcing.constantField κ hκ)).1
    · simp [w]
    · simpa [w,norm_neg] using (od 3 4 hκ (AdditiveHaarForcing.constantField κ hκ)).1
    · simpa [w,norm_neg] using (od 4 5 hκ (AdditiveHaarForcing.constantField κ hκ)).1
  have he (q : HaarNode) : additive q=∑ i,w i q ∧ residual q=∑ i,v i q := by
    simp only [w,v,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,diff,additive,residual]
    constructor <;> abel
  have hpoint (q : HaarNode) : ‖additive q‖^2+‖residual q‖^2≤6*∑ i:Fin 6,(‖w i q‖^2+‖v i q‖^2) := by
    rw [(he q).1,(he q).2,Finset.sum_add_distrib,mul_add]
    exact add_le_add (ScalarHeatGammaSlots.norm_sum_sq_le _) (ScalarHeatGammaSlots.norm_sum_sq_le _)
  have hsum : Summable (fun q=>6*∑ i:Fin 6,(‖w i q‖^2+‖v i q‖^2)):=
    (summable_sum (fun i _=>(hw i).add (hv i))).mul_left 6
  have hactual : Summable (fun q=>‖additive q‖^2+‖residual q‖^2):=
    Summable.of_nonneg_of_le (fun _=>add_nonneg (sq_nonneg _) (sq_nonneg _)) hpoint hsum
  refine ⟨hactual,?_⟩
  have hstart:=hactual.tsum_le_tsum hpoint hsum
  rw [tsum_mul_left] at hstart
  rw [show (∑' q,∑ i:Fin 6,(‖w i q‖^2+‖v i q‖^2))=
    ∑ i:Fin 6,((∑' q,‖w i q‖^2)+(∑' q,‖v i q‖^2)) by
      rw [Summable.tsum_finsetSum (fun i _=>(hw i).add (hv i))]
      simp only [(hw _).tsum_add (hv _)]] at hstart
  have h1:=(od 0 1 hm c1).2
  have h2:=(od 1 2 hm c1).2
  have h4:=(od 3 4 hm r1).2
  have h5:=(od 4 5 hm r1).2
  have a1:=(od 0 1 hκ (AdditiveHaarForcing.constantField κ hκ)).2
  have a2:=(od 1 2 hκ (AdditiveHaarForcing.constantField κ hκ)).2
  have a4:=(od 3 4 hκ (AdditiveHaarForcing.constantField κ hκ)).2
  have a5:=(od 4 5 hκ (AdditiveHaarForcing.constantField κ hκ)).2
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,w,v,norm_neg,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),tsum_zero] at hstart
  have hs0b:=hs0.2
  have hs3b:=hs3.2
  change (∑' q,‖col 0 c0.1 q-col 0 c1.1 q‖^2)≤R0 at hs0b
  change (∑' q,‖-(col 3 r0.1 q-col 3 r1.1 q)‖^2)≤R3 at hs3b
  simp only [norm_neg] at hs3b
  dsimp only [R0,R3,T] at *
  nlinarith [hs0b,hs3b]

end SHE.NativePairedGammaTrace
