module
public import SHE.NativeFullRateCap
public import SHE.NativeHigherRateChoice
public import SHE.StateBands
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeHigherMasterCoefficient
open Real Filter Topology
open scoped NNReal ENNReal BigOperators

def weights(aC aP aG aB:ℝ≥0∞)(Cc Ci Cp Cg Cb:ℝ):Fin 4→ℝ≥0∞:=
  ![aC*(ENNReal.ofReal Ci+ENNReal.ofReal Cc),aP*ENNReal.ofReal Cp,
    2*aG*ENNReal.ofReal Cg,2*aB*ENNReal.ofReal Cb]

def constant(aC aP aG aB:ℝ≥0∞)(Cc Ci Cp Cg Cb:ℝ)(q:Fin 4→ℝ):ℝ:=
  1+∑i:Fin 4,sqrt (weights aC aP aG aB Cc Ci Cp Cg Cb i).toReal*
    StateBands.geometricConstant (q i/2)

private theorem geometric_nonneg{q:ℝ}(hq:0≤q):0≤StateBands.geometricConstant q:=by
  unfold StateBands.geometricConstant
  apply inv_nonneg.mpr
  have he:=rpow_le_one_of_one_le_of_nonpos (by norm_num:(1:ℝ)≤2) (neg_nonpos.mpr hq)
  linarith

theorem constant_nonneg(aC aP aG aB:ℝ≥0∞)(Cc Ci Cp Cg Cb:ℝ)
    (q:Fin 4→ℝ)(hq:∀i,0<q i):0≤constant aC aP aG aB Cc Ci Cp Cg Cb q:=by
  apply add_nonneg zero_le_one
  exact Finset.sum_nonneg (fun i _=>mul_nonneg (sqrt_nonneg _)
    (geometric_nonneg (by linarith only [hq i])))

private theorem power_sq{m a:ℝ}(hm:0≤m):(m^2)^a=(m^a)^2:=by
  rw [←rpow_natCast_mul hm,←rpow_mul_natCast hm]
  congr 1
  ring

private theorem frequency{Λ R q:ℝ}(hΛ:1≤Λ)(hR:Λ^(1/4:ℝ)≤R)(hq:0<q):
    R^(-(q/2))≤Λ^(-(q/8)):=by
  have hΛ0:0<Λ:=zero_lt_one.trans_le hΛ
  have hp:0<Λ^(1/4:ℝ):=rpow_pos_of_pos hΛ0 _
  have hh:=Real.rpow_le_rpow_of_nonpos hp hR (by linarith only [hq]:-(q/2)≤0)
  rw [←rpow_mul hΛ0.le] at hh
  convert hh using 1 <;> congr 1 <;> ring

/-- The literal four common higher-noise coefficients yield their
four separate RMS rates. The current row has no artificial damping
gain, and the signed-good row uses the true negative input energy. -/
theorem cap(aC aP aG aB:ℝ≥0∞)(Cc Ci Cp Cg Cb:ℝ)
    (q:Fin 4→ℝ)(hq:∀i,0<q i){Λ R m H χ:ℝ}(Neg:ℝ≥0∞)
    (hΛ:1≤Λ)(hR:Λ^(1/4:ℝ)≤R)(hm:0≤m)(hH0:0≤H)(hH1:H≤1)(hχ:χ≤1):
    let K:=NativeFullRateCap.coefficient aC aP aG aB Cc Ci Cp Cg Cb (m^2) H χ Neg
    let v:Fin 4→ℝ:=![m^χ,m,sqrt Neg.toReal,1]
    (∑i:Fin 4,sqrt (K i).toReal*StateBands.geometricConstant (q i/2)*R^(-(q i/2)))≤
      constant aC aP aG aB Cc Ci Cp Cg Cb q*(∑i:Fin 4,Λ^(-(q i/8))*v i):=by
  intro K v
  let w:=weights aC aP aG aB Cc Ci Cp Cg Cb
  have hHp1:H^(1-χ)≤1:=rpow_le_one hH0 hH1 (by linarith only [hχ])
  have hs(i:Fin 4):sqrt (K i).toReal≤sqrt (w i).toReal*v i:=by
    fin_cases i
    · change sqrt ((w 0*(ENNReal.ofReal (m^2)^χ*ENNReal.ofReal H^(1-χ))).toReal)≤_
      rw [ENNReal.toReal_mul,ENNReal.toReal_mul,←ENNReal.toReal_rpow,←ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal (sq_nonneg m),ENNReal.toReal_ofReal hH0,power_sq hm]
      have hb:(w 0).toReal*((m^χ)^2*H^(1-χ))≤(w 0).toReal*(m^χ)^2:=by
        nlinarith only [hHp1,mul_nonneg (ENNReal.toReal_nonneg (a:=w 0)) (sq_nonneg (m^χ))]
      apply (sqrt_le_sqrt hb).trans_eq
      rw [sqrt_mul ENNReal.toReal_nonneg,sqrt_sq (rpow_nonneg hm χ)]
      rfl
    · change sqrt ((w 1*ENNReal.ofReal (m^2)).toReal)≤_
      rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg m),
        sqrt_mul ENNReal.toReal_nonneg,sqrt_sq hm]
      rfl
    · change sqrt ((w 2*Neg).toReal)≤_
      rw [ENNReal.toReal_mul,sqrt_mul ENNReal.toReal_nonneg]
      rfl
    · change sqrt ((w 3*ENNReal.ofReal H).toReal)≤_
      rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hH0]
      have hb:(w 3).toReal*H≤(w 3).toReal:=by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hH1 (ENNReal.toReal_nonneg (a:=w 3))
      change sqrt ((w 3).toReal*H)≤sqrt (w 3).toReal*1
      simpa only [mul_one] using sqrt_le_sqrt hb
  let d:Fin 4→ℝ:=fun i=>sqrt (w i).toReal*StateBands.geometricConstant (q i/2)
  have hd(i:Fin 4):0≤d i:=mul_nonneg (sqrt_nonneg _)
    (geometric_nonneg (by linarith only [hq i]))
  have hv(i:Fin 4):0≤v i:=by fin_cases i <;> dsimp [v] <;> positivity
  have hC(i:Fin 4):d i≤constant aC aP aG aB Cc Ci Cp Cg Cb q:=by
    have hh:d i≤∑j:Fin 4,d j:=Finset.single_le_sum (fun j _=>hd j) (Finset.mem_univ i)
    change d i≤1+∑j:Fin 4,d j
    linarith only [hh]
  calc
    _≤∑i:Fin 4,d i*(Λ^(-(q i/8))*v i):=by
      apply Finset.sum_le_sum
      intro i _
      have hg:0≤StateBands.geometricConstant (q i/2):=geometric_nonneg (by linarith only [hq i])
      have hr:0≤R^(-(q i/2)):=rpow_nonneg ((rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _).le.trans hR) _
      have h1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hs i) hg) hr
      have h2:=mul_le_mul_of_nonneg_left (frequency hΛ hR (hq i)) (mul_nonneg (hd i) (hv i))
      dsimp only [d] at h2 ⊢
      nlinarith only [h1,h2]
    _≤∑i:Fin 4,constant aC aP aG aB Cc Ci Cp Cg Cb q*(Λ^(-(q i/8))*v i):=by
      exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hC i)
        (mul_nonneg (rpow_nonneg (zero_lt_one.trans_le hΛ).le _) (hv i)))
    _=_:=by rw [Finset.mul_sum]

end SHE.NativeHigherMasterCoefficient
