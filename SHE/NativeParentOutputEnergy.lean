module

public import SHE.NativeHeatOutputEnergy
public import SHE.NativeGammaAgeValue
public import SHE.FiniteMomentSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SHE.NativeParentOutputEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
open scoped ENNReal BigOperators
local instance nativeParentOutputEnergy_period:Fact (0<2*π):=⟨by positivity⟩
local instance nativeParentOutputEnergy_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance nativeParentOutputEnergy_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

private theorem scaled_envelope (μ:Measure Ω) [IsProbabilityMeasure μ]
    {F:Ω×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀ω y x,‖F (ω,(y,x))‖≤B)
    (a:HeatCircle→ℝ) (ha:Measurable a) (ha0:∀x,0≤a x)
    (hai:Integrable (fun x=>a x^2) haarAddCircle) {E J L:ℝ}
    (he:(∫x,a x^2 ∂haarAddCircle)≤E) (hJ:0≤J) (hL:0<L)
    (k:HeatCircle×HeatCircle→ℝ) (hk:Measurable k) (hk0:∀z,0≤k z)
    (hrow:∀y,Integrable (fun x=>k (y,x)) haarAddCircle ∧ (∫x,k (y,x) ∂haarAddCircle)=L)
    (hcol:∀x,Integrable (fun y=>k (y,x)) haarAddCircle ∧ (∫y,k (y,x) ∂haarAddCircle)=L)
    (hsq:∀x,Integrable (fun y=>k (y,x)^2) haarAddCircle ∧ (∫y,k (y,x)^2 ∂haarAddCircle)≤J)
    (hsharp:∀y x,ProfileL2.normTwo μ (fun ω=>‖F (ω,(y,x))‖)≤a x*k (y,x))
    {Λ ρ t:ℝ} (hΛ:1≤Λ) (hρ:0<ρ) (hρhalf:ρ<1/2) (ht:0<t) (ht1:t≤1):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ)≤
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeHeatSpan.clock t)^(ρ-1/2))*(L^2*E)+
          (NativeHeatSpan.clock t)^ρ*(J*E):=by
  have hnorm(y:HeatCircle):Integrable (fun x=>k (y,x)/L) haarAddCircle ∧
      (∫x,k (y,x)/L ∂haarAddCircle)=1:=by
    refine ⟨(hrow y).1.div_const _,?_⟩
    rw [integral_div,(hrow y).2,div_self hL.ne']
  have hnorm'(x:HeatCircle):Integrable (fun y=>k (y,x)/L) haarAddCircle ∧
      (∫y,k (y,x)/L ∂haarAddCircle)≤1:=by
    refine ⟨(hcol x).1.div_const _,?_⟩
    rw [integral_div,(hcol x).2,div_self hL.ne']
  have hnormsq(x:HeatCircle):Integrable (fun y=>(k (y,x)/L)^2) haarAddCircle ∧
      (∫y,(k (y,x)/L)^2 ∂haarAddCircle)≤J/L^2:=by
    simp_rw [div_pow]
    refine ⟨(hsq x).1.div_const _,?_⟩
    rw [integral_div]
    exact div_le_div_of_nonneg_right (hsq x).2 (sq_nonneg _)
  have hai':Integrable (fun x=>(L*a x)^2) haarAddCircle:=by
    simpa only [mul_pow] using hai.const_mul (L^2)
  have he':(∫x,(L*a x)^2 ∂haarAddCircle)≤L^2*E:=by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
  have hh:=NativeKernelOutputEnergy.from_rms_envelope μ hF hB hb
    (fun x=>L*a x) (ha.const_mul L) (fun x=>mul_nonneg hL.le (ha0 x)) hai' he'
    (div_nonneg hJ (sq_nonneg _)) (fun z=>k z/L) (hk.div_const L)
    (fun z=>div_nonneg (hk0 z) hL.le) hnorm hnorm' hnormsq
    (fun y x=>by convert! hsharp y x using 1; field_simp) hΛ hρ hρhalf ht ht1
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  field_simp

private theorem heat_square_mass {t:ℝ} (ht:0<t) (ht1:t≤1) (c:HeatCircle):
    (∫y:HeatCircle,‖NativeHeatSpan.kernel (8*t) (by positivity) c y‖^2 ∂haarAddCircle)≤
      GaussianNegativePacket.traceConstant*(NativeHeatSpan.clock t)^(-(1/2:ℝ)):=by
  have he:(∫y:HeatCircle,‖NativeHeatSpan.kernel (8*t) (by positivity) c y‖^2 ∂haarAddCircle)=‖circleHeat (8*t) c‖^2:=by
    rw [L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [ProfileVariance.heatPhysical_ae (by positivity:0<8*t) c] with y hy
    change ‖NativeHeatSpan.kernel (8*t) (by positivity) c y‖^2=‖circleHeat (8*t) c y‖^2
    rw [NativeHeatSpan.kernel_eq_physical,hy]
  rw [he,←NativeHeatSpan.push_unit_kernel,CircleNormalization.push.norm_map]
  have hct:NativeHeatSpan.clock (8*t)=8*NativeHeatSpan.clock t:=by unfold NativeHeatSpan.clock;ring
  rw [hct]
  have hc:NativeHeatSpan.clock t≤1:=
    (div_le_one (by positivity:0<4*π^2)).mpr (ht1.trans (by nlinarith [Real.two_le_pi]))
  exact GaussianNegativePacket.kernel_eight_norm_sq (NativeHeatSpan.clock_pos ht) hc _

/-- All actual native score parents are retained. Their quarter-age
weights cancel the L2 heat singularities, and a single Nash cutoff at
root age w yields the required w^rho gain for a variable output amplitude. -/
theorem energy (μ:Measure Ω) [IsProbabilityMeasure μ]
    {F:Ω×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀ω y x,‖F (ω,(y,x))‖≤B)
    (a:HeatCircle→ℝ) (ha:Measurable a) (ha0:∀x,0≤a x)
    (hai:Integrable (fun x=>a x^2) haarAddCircle) {E:ℝ}
    (he:(∫x,a x^2 ∂haarAddCircle)≤E)
    (n:ℕ) (hn:0<n) (age:Fin n→ℝ) (shift:Fin n→HeatCircle)
    (hage:∀i,0<age i) {w:ℝ} (hw:0<w) (hw1:w≤1) (hmax:∀i,age i≤w)
    {Λ ρ:ℝ} (hΛ:1≤Λ) (hρ:0<ρ) (hρhalf:ρ<1/2)
    (hsharp:∀y x,ProfileL2.normTwo μ (fun ω=>‖F (ω,(y,x))‖)≤
      a x*∑i,(age i)^(1/4:ℝ)*‖NativeHeatSpan.kernel (8*age i) (by have := hage i; positivity) y (x+shift i)‖):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ)≤
        (n:ℝ)^2*(4*π^2)^(1/2:ℝ)*GaussianNegativePacket.constant ρ*
          (NativeHeatSpan.clock w)^ρ*E:=by
  let K:Fin n→HeatCircle×HeatCircle→ℝ:=fun i z=>‖NativeHeatSpan.kernel (8*age i) (by have := hage i; positivity) z.1 (z.2+shift i)‖
  let weight:Fin n→ℝ:=fun i=>(age i)^(1/4:ℝ)
  let k:HeatCircle×HeatCircle→ℝ:=fun z=>∑i,weight i*K i z
  let L:ℝ:=∑i,weight i
  let Q:ℝ:=(4*π^2)^(1/2:ℝ)
  let J:ℝ:=(n:ℝ)^2*GaussianNegativePacket.traceConstant*Q
  have hQi:0≤Q:=rpow_nonneg (by positivity) _
  have hJ:0≤J:=mul_nonneg (mul_nonneg (sq_nonneg _) GaussianNegativePacket.traceConstant_pos.le) hQi
  have hkm:∀i,Continuous (K i):=by
    intro i
    simp_rw [K,NativeHeatSpan.kernel_eq_physical]
    exact ((NativeHeatSpan.continuous_heatPhysical_space (by have := hage i; positivity:0<8*age i)).comp
      (continuous_fst.prodMk (continuous_snd.add continuous_const))).norm
  have hkc:Continuous k:=continuous_finset_sum _ (fun i _=>(hkm i).const_mul _)
  have hweight(i:Fin n):0<weight i:=rpow_pos_of_pos (hage i) _
  have hL:0<L:=Finset.sum_pos (fun i _=>hweight i) ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have hki(i:Fin n)(y:HeatCircle):Integrable (fun x=>K i (y,x)) haarAddCircle:=
    ((hkm i).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hkir(i:Fin n)(x:HeatCircle):Integrable (fun y=>K i (y,x)) haarAddCircle:=
    ((hkm i).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hkr(i:Fin n)(y:HeatCircle):(∫x,K i (y,x) ∂haarAddCircle)=1:=by
    exact (integral_add_right_eq_self (μ:=haarAddCircle)
      (fun x:HeatCircle=>‖NativeHeatSpan.kernel (8*age i) (by have := hage i; positivity) y x‖) (shift i)).trans
        (NativeHeatSpan.kernel_norm_mass (by have := hage i; positivity) y)
  have hkl(i:Fin n)(x:HeatCircle):(∫y,K i (y,x) ∂haarAddCircle)=1:=by
    change (∫y:HeatCircle,‖NativeHeatSpan.kernel (8*age i) (by have := hage i; positivity) y (x+shift i)‖ ∂haarAddCircle)=1
    conv_lhs => arg 2; ext y; rw [NativeHeatSpan.kernel_symm (by have := hage i; positivity:0<8*age i) y (x+shift i)]
    exact NativeHeatSpan.kernel_norm_mass (by have := hage i; positivity) _
  have hrow(y:HeatCircle):Integrable (fun x=>k (y,x)) haarAddCircle ∧ (∫x,k (y,x) ∂haarAddCircle)=L:=by
    refine ⟨integrable_finsetSum _ (fun i _=>(hki i y).const_mul _),?_⟩
    rw [show (fun x=>k (y,x))=(fun x=>∑i,weight i*K i (y,x)) from rfl,
      integral_finsetSum _ (fun i _=>(hki i y).const_mul _)]
    simp_rw [integral_const_mul,hkr,mul_one]
    rfl
  have hcol(x:HeatCircle):Integrable (fun y=>k (y,x)) haarAddCircle ∧ (∫y,k (y,x) ∂haarAddCircle)=L:=by
    refine ⟨integrable_finsetSum _ (fun i _=>(hkir i x).const_mul _),?_⟩
    rw [show (fun y=>k (y,x))=(fun y=>∑i,weight i*K i (y,x)) from rfl,
      integral_finsetSum _ (fun i _=>(hkir i x).const_mul _)]
    simp_rw [integral_const_mul,hkl,mul_one]
    rfl
  have hsingle(i:Fin n)(x:HeatCircle):(∫y,(weight i*K i (y,x))^2 ∂haarAddCircle)≤GaussianNegativePacket.traceConstant*Q:=by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hh:=mul_le_mul_of_nonneg_left (heat_square_mass (hage i) ((hmax i).trans hw1) (x+shift i)) (sq_nonneg (weight i))
    simp_rw [←NativeHeatSpan.kernel_symm (by have := hage i; positivity:0<8*age i)] at hh
    apply hh.trans_eq
    rw [show weight i^2=(age i)^(1/2:ℝ) by
      dsimp [weight];rw [←Real.rpow_mul_natCast (hage i).le];congr 1;norm_num]
    rw [NativeGammaAgeValue.clock_power (hage i).le]
    have hcancel:(age i)^(1/2:ℝ)*(age i)^(-(1/2:ℝ))=1:=by
      rw [←Real.rpow_add (hage i)]
      norm_num
    calc
      _=GaussianNegativePacket.traceConstant*Q*((age i)^(1/2:ℝ)*(age i)^(-(1/2:ℝ))):=by
        dsimp [Q];norm_num only [neg_neg];ring
      _=_:=by rw [hcancel,mul_one]
  have hsq(x:HeatCircle):Integrable (fun y=>k (y,x)^2) haarAddCircle ∧ (∫y,k (y,x)^2 ∂haarAddCircle)≤J:=by
    have hi:Integrable (fun y=>k (y,x)^2) haarAddCircle:=
      ((hkc.comp (continuous_id.prodMk continuous_const)).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have his(i:Fin n):Integrable (fun y=>(weight i*K i (y,x))^2) haarAddCircle:=
      ((((hkm i).comp (continuous_id.prodMk continuous_const)).const_mul _).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    refine ⟨hi,?_⟩
    have hs(y:HeatCircle):k (y,x)^2≤(n:ℝ)*∑i,(weight i*K i (y,x))^2:=by
      simpa only [k,Fintype.card_fin,show 2-1=1 from rfl,pow_one] using
        FiniteMomentSum.sum_pow_le 2 (by norm_num) (fun i=>weight i*K i (y,x))
          (fun i=>mul_nonneg (hweight i).le (norm_nonneg _))
    apply (integral_mono hi ((integrable_finsetSum _ (fun i _=>his i)).const_mul _) hs).trans
    rw [integral_const_mul,integral_finsetSum _ (fun i _=>his i)]
    have hsum:(∑i:Fin n,∫y:HeatCircle,(weight i*K i (y,x))^2 ∂haarAddCircle)≤
        ∑_:Fin n,GaussianNegativePacket.traceConstant*Q:=Finset.sum_le_sum (fun i _=>hsingle i x)
    have hbnd:=mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,J,pow_two,mul_assoc] using hbnd
  have hh:=scaled_envelope μ hF hB hb a ha ha0 hai he hJ hL k hkc.measurable
    (fun z=>Finset.sum_nonneg (fun i _=>mul_nonneg (hweight i).le (norm_nonneg _)))
    hrow hcol hsq hsharp hΛ hρ hρhalf hw hw1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hE:0≤E:=(integral_nonneg (fun x=>sq_nonneg (a x))).trans he
  have hLbound:L≤(n:ℝ)*w^(1/4:ℝ):=by
    exact (Finset.sum_le_sum (fun i _=>rpow_le_rpow (hage i).le (hmax i) (by norm_num))).trans_eq (by simp [L,weight])
  have hLsq:L^2≤(n:ℝ)^2*w^(1/2:ℝ):=by
    have hh:=pow_le_pow_left₀ hL.le hLbound 2
    rw [mul_pow,←Real.rpow_mul_natCast hw.le] at hh
    norm_num only at hh
    convert! hh using 1
  have hc:0≤(1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeHeatSpan.clock w)^(ρ-1/2):=by
    have hg:0≤HeatTrace.fractionalGaussianIntegral ρ:=(HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
    exact mul_nonneg (by positivity) (rpow_nonneg (NativeHeatSpan.clock_pos hw).le _)
  apply (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLsq hE) hc) le_rfl).trans_eq
  rw [NativeGammaAgeValue.clock_power hw.le (ρ-1/2),NativeGammaAgeValue.clock_power hw.le ρ]
  dsimp only [J,Q]
  have hp:w^(ρ-1/2)*w^(1/2:ℝ)=w^ρ:=by rw [←Real.rpow_add hw];congr 1;ring
  have hd:(4*π^2)^(-(ρ-1/2))=(4*π^2)^(1/2:ℝ)*(4*π^2)^(-ρ):=by
    rw [←Real.rpow_add (by positivity:0<4*π^2)];congr 1;ring
  rw [hd]
  calc
    _=(n:ℝ)^2*(4*π^2)^(1/2:ℝ)*
        (1+2*HeatTrace.fractionalGaussianIntegral ρ+GaussianNegativePacket.traceConstant)*
          ((4*π^2)^(-ρ)*w^ρ)*E:=by rw [←hp];ring
    _=_:=rfl

end SHE.NativeParentOutputEnergy
