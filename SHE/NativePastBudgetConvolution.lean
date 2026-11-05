module

public import SHE.NativeCurrentBudgetFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativePastBudgetConvolution
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition AllocatedAssignmentKernel
  MeanRMSTimeFactors QuarterRMSTimeFactors PhysicalAssignmentGapScale
open scoped BigOperators
open Classical

/-- The true past-age half-power remains integrable after native
old-time averaging. Its actual h^(-1/2) cost is explicit and the
frequency constant is uniform before the band window is chosen. -/
theorem weighted_bound {d:ℝ}(hd:0<d)(m:ℕ){η:ℝ}(hη:0<η):
    ∃C:ℝ,0<C ∧ ∀ν h:ℝ,0<ν→0<h→h≤1→
      Integrable (fun s=>s^(-(1/2:ℝ))*(h-s)^(d-1)*rootMass ν (h-s)^m)
        (volume.restrict (Ioc 0 h)) ∧
      (∫s,s^(-(1/2:ℝ))*(h-s)^(d-1)*rootMass ν (h-s)^m ∂volume.restrict (Ioc 0 h))≤
        C*h^(-(1/2:ℝ))*(1+ν)^η:=by
  let ε:=η/(4*((m:ℝ)+1))
  let K:=4+1/ε
  have hε:0<ε:=by dsimp only [ε];positivity
  have hK:0<K:=by dsimp only [K];positivity
  let C:=2*(2+1/d)*K^m
  have hC:0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro ν h hν hh hh1
  let M:=rootMass ν h^m
  have hM:0≤M:=pow_nonneg (rootMass_nonneg hν.le hh.le) _
  have hpair:IntervalIntegrable (fun s=>s^(-(1/2:ℝ))*(h-s)^(d-1)) volume 0 h:=by
    simpa only [show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num] using
      positive_power_pair_intervalIntegrable (by norm_num : (0:ℝ)<1/2) hd hh.le
  have hmaj:Integrable (fun s=>M*(s^(-(1/2:ℝ))*(h-s)^(d-1))) (volume.restrict (Ioc 0 h)):=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).mp hpair).const_mul M
  have hmeas:Measurable (fun s:ℝ=>s^(-(1/2:ℝ))*(h-s)^(d-1)*rootMass ν (h-s)^m):=
    ((real_rpow_measurable _).mul ((measurable_const.sub measurable_id).pow_const _)).mul
      (((rootMass_measurable ν).comp (measurable_const.sub measurable_id)).pow_const m)
  have hevent:∀ᵐs:ℝ∂volume.restrict (Ioc 0 h),s∈Ioo 0 h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hbound:∀ᵐs:ℝ∂volume.restrict (Ioc 0 h),
      s^(-(1/2:ℝ))*(h-s)^(d-1)*rootMass ν (h-s)^m≤M*(s^(-(1/2:ℝ))*(h-s)^(d-1)):=by
    filter_upwards [hevent] with s hs
    have hpow:rootMass ν (h-s)^m≤M:=pow_le_pow_left₀
      (rootMass_nonneg hν.le (by linarith [hs.2] : 0≤h-s))
      (rootMass_mono hν.le (by linarith [hs.2]) (by linarith [hs.1])) m
    convert! mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (Real.rpow_nonneg hs.1.le _) (Real.rpow_nonneg (by linarith [hs.2] : 0≤h-s) _)) using 1 <;> ring
  have hi:Integrable (fun s=>s^(-(1/2:ℝ))*(h-s)^(d-1)*rootMass ν (h-s)^m)
      (volume.restrict (Ioc 0 h)):=by
    apply hmaj.mono' hmeas.aestronglyMeasurable
    filter_upwards [hevent,hbound] with s hs hbs
    rw [Real.norm_eq_abs,abs_of_nonneg]
    · exact hbs
    · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.1.le _)
        (Real.rpow_nonneg (by linarith [hs.2] : 0≤h-s) _))
        (pow_nonneg (rootMass_nonneg hν.le (by linarith [hs.2])) _)
  refine ⟨hi,?_⟩
  have hp: (∫s,s^(-(1/2:ℝ))*(h-s)^(d-1) ∂volume.restrict (Ioc 0 h))≤
      2*(2+1/d)*h^(d-(1/2:ℝ)):=by
    rw [←intervalIntegral.integral_of_le hh.le]
    have hb:=positive_power_convolution_le (by norm_num : (0:ℝ)<1/2) hd hh
    simpa only [show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num,
      show 1/(1/2:ℝ)=2 by norm_num,show (1/2:ℝ)+d-1=d-(1/2:ℝ) by ring] using hb
  have hpow:h^(d-(1/2:ℝ))≤h^(-(1/2:ℝ)):=by
    have hs:h^d≤1:=Real.rpow_le_one hh.le hh1 hd.le
    rw [show d-(1/2:ℝ)=d+(-(1/2:ℝ)) by ring,Real.rpow_add hh]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hh.le _) hs
  have hfreq:M≤K^m*(1+ν)^η:=by
    let S:ℝ:=(1+ν)^(4*ε)
    have hS:1≤S:=Real.one_le_rpow (by linarith) (by positivity)
    have hr:rootMass ν h≤K*S:=rootMass_frequency_bound hν.le hh.le hh1 hε
    have hm:rootMass ν h^m≤K^m*S^m:=by
      simpa only [mul_pow] using pow_le_pow_left₀ (rootMass_nonneg hν.le hh.le) hr m
    have hs:S^m≤S^(m+1):=by rw [pow_succ];exact le_mul_of_one_le_right (pow_nonneg (by linarith : 0≤S) _) hS
    have he:S^(m+1)=(1+ν)^η:=by
      dsimp only [S]
      rw [←Real.rpow_mul_natCast (by positivity : 0≤1+ν)]
      congr 1
      dsimp only [ε]
      push_cast
      field_simp
    exact hm.trans ((mul_le_mul_of_nonneg_left hs (pow_nonneg hK.le _)).trans_eq (by rw [he]))
  apply (integral_mono_ae hi hmaj hbound).trans
  rw [integral_const_mul]
  have hp2: (∫s,s^(-(1/2:ℝ))*(h-s)^(d-1) ∂volume.restrict (Ioc 0 h))≤
      2*(2+1/d)*h^(-(1/2:ℝ)):=hp.trans
        (mul_le_mul_of_nonneg_left hpow (by positivity))
  calc
    _≤M*(2*(2+1/d)*h^(-(1/2:ℝ))):=mul_le_mul_of_nonneg_left hp2 hM
    _≤(K^m*(1+ν)^η)*(2*(2+1/d)*h^(-(1/2:ℝ))):=
      mul_le_mul_of_nonneg_right hfreq (by positivity)
    _=_:=by dsimp only [C];ring


/-- The full native past-residual time majorant, after ALL actual old
assignments are summed. The explicit half-power loss is uniform before
both the frequency and the actual moving window are chosen. -/
theorem majorant_energy (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(Cs:ℕ→ℝ)
    (k:ℕ)(ρ:ℝ)(hρ:0<ρ)(η:ℝ)(hη:0<η):
    ∃C:ℝ,0<C ∧ ∀ν h:ℝ,0<ν→0<h→h≤1→
      Integrable (fun s=>s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν (h-s)^2)
        (volume.restrict (Ioc 0 h)) ∧
      (∫s,s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν (h-s)^2
        ∂volume.restrict (Ioc 0 h))≤C*h^(-(1/2:ℝ))*(1+ν)^η:=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  let c:=Real.sqrt (ProfileVariance.upperConstant*(P.lower/2))
  have hc:0<c:=Real.sqrt_pos.mpr (mul_pos ProfileVariance.upperConstant_pos (by linarith [P.lower_pos]))
  let d:=fun i:Fin cs.length=>ρ+P.exponent*(roughCount (cs.get i):ℝ)/2
  have hd(i:Fin cs.length):0<d i:=by
    apply add_pos_of_pos_of_nonneg hρ
    exact div_nonneg (mul_nonneg P.exponent_pos.le (Nat.cast_nonneg _)) (by norm_num)
  choose C hCpos hCb using (fun i:Fin cs.length=>weighted_bound (hd i) (2*rootCount (cs.get i)) hη)
  let B:ℝ:=(cs.length:ℝ)*∑i:Fin cs.length,
    (assignmentCoefficient P ell Cs k 1 (1/2:ℝ) 1 i)^2*C i*(1+c)^η
  have hB:0≤B:=by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (sq_nonneg _) (hCpos i).le)
      (Real.rpow_nonneg (by positivity) _))
  refine ⟨1+B,by linarith,?_⟩
  intro ν h hν hh hh1
  let f:=fun i:Fin cs.length=>fun s=>|assignmentCoefficient P ell Cs k 1 (1/2:ℝ) 1 i| * 
    |squareKernel ρ P.exponent (ν*c) (rootCount (cs.get i)) (roughCount (cs.get i)) (h-s)|
  have hevent:∀ᵐs:ℝ∂volume.restrict (Ioc 0 h),s∈Ioo 0 h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have he(i:Fin cs.length):(fun s=>s^(-(1/2:ℝ))*f i s^2)=ᵐ[volume.restrict (Ioc 0 h)]
      (fun s=>(assignmentCoefficient P ell Cs k 1 (1/2:ℝ) 1 i)^2*
        (s^(-(1/2:ℝ))*(h-s)^(d i-1)*rootMass (ν*c) (h-s)^(2*rootCount (cs.get i)))):=by
    filter_upwards [hevent] with s hs
    dsimp only [f]
    rw [mul_pow,sq_abs,sq_abs,MeanRMSTimeFactors.squareKernel,mul_pow,
      ←Real.rpow_mul_natCast (by linarith [hs.2] : 0≤h-s),←pow_mul,Nat.mul_comm (rootCount (cs.get i)) 2]
    have hexp:(ρ/2+P.exponent*(roughCount (cs.get i):ℝ)/4-1/2)*(2:ℕ)=d i-1:=by
      dsimp only [d]
      norm_num
      ring
    rw [hexp]
    ring
  have hi(i:Fin cs.length):Integrable (fun s=>s^(-(1/2:ℝ))*f i s^2) (volume.restrict (Ioc 0 h)):=
    (((hCb i (ν*c) h (mul_pos hν hc) hh hh1).1).const_mul
      ((assignmentCoefficient P ell Cs k 1 (1/2:ℝ) 1 i)^2)).congr (he i).symm
  have hpow:(1+ν*c)^η≤(1+c)^η*(1+ν)^η:=by
    have hh:=Real.rpow_le_rpow (by positivity : 0≤1+ν*c)
      (show 1+ν*c≤(1+c)*(1+ν) by nlinarith) hη.le
    rwa [Real.mul_rpow (by positivity : 0≤1+c) (by positivity : 0≤1+ν)] at hh
  have hib(i:Fin cs.length):(∫s,s^(-(1/2:ℝ))*f i s^2 ∂volume.restrict (Ioc 0 h))≤
      (assignmentCoefficient P ell Cs k 1 (1/2:ℝ) 1 i)^2*C i*(1+c)^η*h^(-(1/2:ℝ))*(1+ν)^η:=by
    rw [integral_congr_ae (he i),integral_const_mul]
    have hb:=(hCb i (ν*c) h (mul_pos hν hc) hh hh1).2
    have hb':(∫s,s^(-(1/2:ℝ))*(h-s)^(d i-1)*rootMass (ν*c) (h-s)^(2*rootCount (cs.get i))
        ∂volume.restrict (Ioc 0 h))≤C i*h^(-(1/2:ℝ))*((1+c)^η*(1+ν)^η):=
      hb.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hCpos i).le (Real.rpow_nonneg hh.le _)))
    convert! mul_le_mul_of_nonneg_left hb'
      (sq_nonneg (assignmentCoefficient P ell Cs k 1 (1/2:ℝ) 1 i)) using 1 <;> ring
  let G:=fun s=>s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν (h-s)^2
  have hGm:Measurable G:=(real_rpow_measurable _).mul
    (((NativeCurrentBudgetFrequency.majorant_measurable P ell Cs k ρ 0 ν).comp
      (measurable_const.sub measurable_id)).pow_const 2)
  have hGi:Integrable (fun s=>(cs.length:ℝ)*∑i:Fin cs.length,s^(-(1/2:ℝ))*f i s^2)
      (volume.restrict (Ioc 0 h)):=
    (integrable_finsetSum Finset.univ (fun i _=>hi i)).const_mul _
  have hb:∀ᵐs:ℝ∂volume.restrict (Ioc 0 h),G s≤(cs.length:ℝ)*∑i:Fin cs.length,s^(-(1/2:ℝ))*f i s^2:=by
    filter_upwards [hevent] with s hs
    have hfinite:(∑i:Fin cs.length,f i s)^2≤(cs.length:ℝ)*∑i:Fin cs.length,f i s^2:=by
      simpa only [Fintype.card_fin,show 2-1=1 from rfl,pow_one] using
        FiniteMomentSum.sum_pow_le 2 (by norm_num) (fun i:Fin cs.length=>f i s)
          (fun i=>mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have heq:NativeCurrentBudgetFrequency.majorant P ell Cs k ρ 0 ν (h-s)=∑i:Fin cs.length,f i s:=by
      dsimp only [NativeCurrentBudgetFrequency.majorant,f,c,cs]
      norm_num only [sub_zero,zero_div,show (2:ℝ)/4=1/2 by norm_num]
    dsimp only [G]
    rw [heq]
    have hm:=mul_le_mul_of_nonneg_left hfinite (Real.rpow_nonneg hs.1.le (-(1/2:ℝ)))
    convert! hm using 1
    simp only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
  have hiG:Integrable G (volume.restrict (Ioc 0 h)):=by
    apply hGi.mono' hGm.aestronglyMeasurable
    filter_upwards [hevent,hb] with s hs hbs
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs.1.le _) (sq_nonneg _))]
    exact hbs
  refine ⟨hiG,?_⟩
  have hhmain:=integral_mono_ae hiG hGi hb
  rw [integral_const_mul,integral_finsetSum _ (fun i _=>hi i)] at hhmain
  apply (hhmain.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>hib i))
    (Nat.cast_nonneg _))).trans
  have heq:(cs.length:ℝ)*∑i:Fin cs.length,
      (assignmentCoefficient P ell Cs k 1 (1/2:ℝ) 1 i)^2*C i*(1+c)^η*h^(-(1/2:ℝ))*(1+ν)^η=
      B*h^(-(1/2:ℝ))*(1+ν)^η:=by
    dsimp only [B]
    simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : B≤1+B) (Real.rpow_nonneg hh.le _))
      (Real.rpow_nonneg (by positivity) _)

end SHE.NativePastBudgetConvolution
