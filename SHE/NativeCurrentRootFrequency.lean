module

public import SHE.NativeCurrentSquareCorners

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeCurrentRootFrequency
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition AllocatedAssignmentKernel
  MeanRMSTimeFactors
open scoped BigOperators

/-- A fixed positive frequency loss bounds the zero, positive and
negative root-square regimes uniformly in every actual window T<=1.
In particular no band-dependent time window is hidden in the constant. -/
theorem weighted_bound {d:ℝ}{m:ℕ}(hdegree:0<d+(m:ℝ)/4){η:ℝ}(hη:0<η):
    ∃C:ℝ,0<C ∧ ∀ν T:ℝ,0<ν→0<T→T≤1→
      (∫w,w^(d-1)*rootMass ν w^m ∂volume.restrict (Ioc 0 T))≤
        C*(1+ν)^(max 0 (-4*d)+η):=by
  let ε:=η/(4*((m:ℝ)+1))
  let K:=4+1/ε
  have hε:0<ε:=by dsimp only [ε];positivity
  have hK:0<K:=by dsimp only [K];positivity
  have hpower(ν:ℝ)(hν:0<ν):((1+ν)^(4*ε))^(m+1)=(1+ν)^η:=by
    rw [←Real.rpow_mul_natCast (by positivity : 0≤1+ν)]
    congr 1
    dsimp only [ε]
    push_cast
    field_simp
  by_cases hd:0<d
  · refine ⟨(1/d)*K^m,by positivity,?_⟩
    intro ν T hν hT hT1
    let S:ℝ:=(1+ν)^(4*ε)
    have hS:1≤S:=Real.one_le_rpow (by linarith) (by positivity)
    have hS0:0≤S:=zero_le_one.trans hS
    have hM:0≤rootMass ν T:=rootMass_nonneg hν.le hT.le
    have hroot:rootMass ν T≤K*S:=rootMass_frequency_bound hν.le hT.le hT1 hε
    have hp:rootMass ν T^m≤K^m*S^m:=by
      simpa only [mul_pow] using pow_le_pow_left₀ hM hroot m
    have hSpow:S^m≤S^(m+1):=by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hS0 _) hS
    have hTpow:T^d≤1:=Real.rpow_le_one hT.le hT1 hd.le
    have hcoef:T^d/d≤1/d:=div_le_div_of_nonneg_right hTpow hd.le
    have hbound:(∫w,w^(d-1)*rootMass ν w^m ∂volume.restrict (Ioc 0 T))≤
        (1/d)*K^m*S^(m+1):=by
      rw [←intervalIntegral.integral_of_le hT.le]
      apply (weighted_root_mass_pos_le hν.le hd hT.le m).trans
      calc
        _≤(1/d)*rootMass ν T^m:=mul_le_mul_of_nonneg_right hcoef (pow_nonneg hM _)
        _≤(1/d)*(K^m*S^m):=mul_le_mul_of_nonneg_left hp (by positivity)
        _≤_:=by
          convert! mul_le_mul_of_nonneg_left hSpow (show 0≤(1/d)*K^m by positivity) using 1 <;> ring
    have hlast:(1+ν)^η≤(1+ν)^(max 0 (-4*d)+η):=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [le_max_left 0 (-4*d)])
    have he:S^(m+1)=(1+ν)^η:=hpower ν hν
    rw [he] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left hlast (by positivity))
  · by_cases hz:d=0
    · have hm:0<m:=by
        by_contra hn
        have hm0:m=0:=Nat.eq_zero_of_not_pos hn
        simp only [hz,hm0,Nat.cast_zero,zero_div,add_zero,lt_self_iff_false] at hdegree
      have hmR:0<(m:ℝ):=by exact_mod_cast hm
      refine ⟨(4/(m:ℝ)+K)*K^m,by positivity,?_⟩
      intro ν T hν hT hT1
      let S:ℝ:=(1+ν)^(4*ε)
      have hS:1≤S:=Real.one_le_rpow (by linarith) (by positivity)
      have hS0:0≤S:=zero_le_one.trans hS
      have hM:0≤rootMass ν T:=rootMass_nonneg hν.le hT.le
      have hroot:rootMass ν T≤K*S:=rootMass_frequency_bound hν.le hT.le hT1 hε
      have hp:rootMass ν T^m≤K^m*S^m:=by
        simpa only [mul_pow] using pow_le_pow_left₀ hM hroot m
      have hleft:4/(m:ℝ)+rootMass ν T≤(4/(m:ℝ)+K)*S:=by
        have hfour:0≤4/(m:ℝ):=by positivity
        have hs:=mul_le_mul_of_nonneg_left hS hfour
        nlinarith
      have hbound:(∫w,w^(d-1)*rootMass ν w^m ∂volume.restrict (Ioc 0 T))≤
          ((4/(m:ℝ)+K)*K^m)*S^(m+1):=by
        rw [hz,zero_sub,←intervalIntegral.integral_of_le hT.le]
        simp_rw [Real.rpow_neg_one]
        have hb:=root_mass_density_integral_le (m:=m) hν hT.le hm
        apply hb.trans
        have hh:=mul_le_mul hleft hp (pow_nonneg hM _) (by positivity : 0≤(4/(m:ℝ)+K)*S)
        convert! hh using 1 <;> rw [pow_succ] <;> ring
      have he:S^(m+1)=(1+ν)^η:=hpower ν hν
      rw [he] at hbound
      simpa only [hz,mul_zero,neg_zero,max_self,zero_add] using hbound
    · have hdneg:d<0:=lt_of_le_of_ne (le_of_not_gt hd) hz
      have hm:0<m:=by
        by_contra hn
        have hm0:m=0:=Nat.eq_zero_of_not_pos hn
        rw [hm0,Nat.cast_zero,zero_div,add_zero] at hdegree
        linarith
      obtain ⟨C,hC,hb⟩:=weighted_root_negative hdneg hm hdegree
      refine ⟨C,hC,?_⟩
      intro ν T hν hT _
      have hbase:ν^(-4*d)≤(1+ν)^(-4*d):=
        Real.rpow_le_rpow hν.le (by linarith) (by linarith)
      have hexp:(1+ν)^(-4*d)≤(1+ν)^(max 0 (-4*d)+η):=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [le_max_right 0 (-4*d)])
      rw [←intervalIntegral.integral_of_le hT.le]
      exact (hb ν T hν hT.le).trans (mul_le_mul_of_nonneg_left (hbase.trans hexp) hC.le)

/-- Every genuine old assignment has the same sufficient frequency
exponent. The rough blocks use their positive beta margin; an all-root
assignment retains the exact zero/negative-degree root-mass regime. -/
theorem assignment_bound {k:ℕ}(cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k))(hk:0<k)
    {ρ χ β:ℝ}(hρ:0<ρ)(hχ:χ<1)(hβ:0<β)(hmargin:χ<β+2*ρ)
    {η:ℝ}(hη:0<η):
    ∃C:ℝ,0<C ∧ ∀ν T:ℝ,0<ν→0<T→T≤1→
      (∫w,squareKernel (ρ-χ/2) β ν (rootCount cs) (roughCount cs) w^2
        ∂volume.restrict (Ioc 0 T))≤C*(1+ν)^(max 0 (2*χ-4*ρ)+η):=by
  let d:=ρ-χ/2+β*(roughCount cs:ℝ)/2
  have hd:0<d+((2*rootCount cs:ℕ):ℝ)/4:=
    NativeCurrentSquareCorners.assignment_degree_pos cs hc hk hρ hχ hβ hmargin
  obtain ⟨C,hC,hb⟩:=weighted_bound hd hη
  refine ⟨C,hC,?_⟩
  intro ν T hν hT hT1
  have he:(fun w=>squareKernel (ρ-χ/2) β ν (rootCount cs) (roughCount cs) w^2)=ᵐ[volume.restrict (Ioc 0 T)]
      (fun w=>w^(d-1)*rootMass ν w^(2*rootCount cs)):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    unfold squareKernel
    rw [mul_pow,←Real.rpow_mul_natCast hw.1.le,←pow_mul,Nat.mul_comm (rootCount cs) 2]
    congr 2
    dsimp only [d]
    ring
  rw [integral_congr_ae he]
  have hdLe:-4*d≤2*χ-4*ρ:=by
    dsimp only [d]
    have hr:(0:ℝ)≤roughCount cs:=Nat.cast_nonneg _
    nlinarith
  have hm:max 0 (-4*d)≤max 0 (2*χ-4*ρ):=max_le_max_left _ hdLe
  exact (hb ν T hν hT hT1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC.le)

end SHE.NativeCurrentRootFrequency
