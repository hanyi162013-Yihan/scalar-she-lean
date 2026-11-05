module
public import SHE.MixedNativeReferenceGaussianFamily
public import SHE.ActualReferenceMasterClosure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeReferenceMasterCoefficient
open Real Filter Topology
open scoped NNReal ENNReal BigOperators

def degrees(β:ℝ)(k:ℕ):Fin 3→ℝ:=
  MixedNativeReferenceGaussianFamily.degrees β (SHE.rho β) (β/100) (β/100) k

def rawConstants(Q:CanonicalCovariance.ProfileParameters)(κ M A:ℝ)(k p:ℕ)
    (Babs B0:ℝ≥0)(β:ℝ):Fin 3→ℝ:=![
  3*A^2*2^(2*(β/100))*PastReferenceBandConstants.covariance Q κ M k Babs (β/100),
  3*A^2*2^(2*(β/100))*PastReferenceBandConstants.baseline Q κ M k Babs (β/100),
  3*A^2*2^(2*(β/100))*PastReferenceBandConstants.mean Q κ M k p B0
    (SHE.rho β) (ActualReferenceMasterClosure.referenceExponent β) (β/100) (β/100)]

def constant(Q:CanonicalCovariance.ProfileParameters)(κ M A:ℝ)(k p:ℕ)
    (Babs B0:ℝ≥0)(β:ℝ):ℝ:=1+∑i:Fin 3,
  sqrt (rawConstants Q κ M A k p Babs B0 β i)*StateBands.geometricConstant (degrees β k i/2)

def linear(β Λ:ℝ):ℝ:=Λ^(-(SHE.rho β)/2)

theorem rawConstants_nonneg(Q:CanonicalCovariance.ProfileParameters)(κ M A:ℝ)(k p:ℕ)
    (Babs B0:ℝ≥0)(β:ℝ)(i:Fin 3):0≤rawConstants Q κ M A k p Babs B0 β i:=by
  fin_cases i
  · have hc:=PastReferenceBandConstants.covariance_nonneg Q κ M k Babs (β/100)
    dsimp [rawConstants];positivity
  · have hc:=PastReferenceBandConstants.baseline_nonneg Q κ M k Babs (β/100)
    dsimp [rawConstants];positivity
  · have hc:=PastReferenceBandConstants.mean_nonneg Q κ M k p B0
      (SHE.rho β) (ActualReferenceMasterClosure.referenceExponent β) (β/100) (β/100)
    dsimp [rawConstants];positivity

theorem degrees_pos{β:ℝ}(hβ:0<β)(hβsmall:β≤4/25)(k:ℕ)(i:Fin 3):0<degrees β k i:=by
  have hh:=PastReferenceBandFrequency.printed_positive hβ hβsmall k
  fin_cases i
  · exact hh.1
  · exact hh.2.1
  · convert hh.2.2 using 1 <;> dsimp [degrees,MixedNativeReferenceGaussianFamily.degrees,SHE.rho] <;> ring

private theorem geometric_nonneg{q:ℝ}(hq:0≤q):0≤StateBands.geometricConstant q:=by
  unfold StateBands.geometricConstant
  apply inv_nonneg.mpr
  have he:=rpow_le_one_of_one_le_of_nonpos (by norm_num:(1:ℝ)≤2) (neg_nonpos.mpr hq)
  linarith

theorem constant_nonneg(Q:CanonicalCovariance.ProfileParameters)(κ M A:ℝ)(k p:ℕ)
    (Babs B0:ℝ≥0){β:ℝ}(hβ:0<β)(hβsmall:β≤4/25):
    0≤constant Q κ M A k p Babs B0 β:=by
  unfold constant
  have hs:0≤∑i:Fin 3,sqrt (rawConstants Q κ M A k p Babs B0 β i)*
      StateBands.geometricConstant (degrees β k i/2):=
    Finset.sum_nonneg (fun i _=>mul_nonneg (sqrt_nonneg _) (geometric_nonneg (by
      exact (div_pos (degrees_pos hβ hβsmall k i) (by norm_num)).le)))
  linarith

private theorem sqrt_rpow{a x:ℝ}(hx:0≤x):sqrt (x^a)=x^(a/2):=by
  rw [sqrt_eq_rpow,←rpow_mul hx]
  congr 1
  ring

private theorem power_sq{m a:ℝ}(hm:0≤m):(m^2)^a=(m^a)^2:=by
  rw [←rpow_natCast_mul hm,←rpow_mul_natCast hm]
  congr 1
  ring

/-- The exact three reference coefficients retain a linear true-energy
row and the additional sublinear reference-mean row. The structural
constant is fixed before damping, energy and the common band cutoff. -/
theorem cap(Q:CanonicalCovariance.ProfileParameters)(κ M A:ℝ)(k p:ℕ)
    (Babs B0:ℝ≥0){β Λ m H R:ℝ}(hβ:0<β)(hβsmall:β≤4/25)
    (hΛ:1≤Λ)(hm:0≤m)(hH0:0≤H)(hH1:H≤1)(hR:1≤R):
    let K:=MixedNativeReferenceGaussianFamily.coefficients Q κ M Λ (m^2) H A k p Babs B0
      (SHE.rho β) (ActualReferenceMasterClosure.referenceExponent β) (β/100) (β/100)
    (∑i:Fin 3,sqrt (K i).toReal*StateBands.geometricConstant (degrees β k i/2)*R^(-(degrees β k i/2)))≤
      constant Q κ M A k p Babs B0 β*
        (linear β Λ*m+Λ^(-β/100)*m^(ActualReferenceMasterClosure.referenceExponent β)):=by
  intro K
  let c:=rawConstants Q κ M A k p Babs B0 β
  let χ:=ActualReferenceMasterClosure.referenceExponent β
  let v:Fin 3→ℝ:=fun i=>if i=2 then Λ^(-β/100)*m^χ else linear β Λ*m
  have hΛ0:0<Λ:=zero_lt_one.trans_le hΛ
  have hc(i:Fin 3):0≤c i:=rawConstants_nonneg Q κ M A k p Babs B0 β i
  have hχ1:χ<1:=(ActualReferenceMasterClosure.reference_admissible hβ hβsmall).2.1
  have hHp:0≤H^(1-χ):=rpow_nonneg hH0 _
  have hHp1:H^(1-χ)≤1:=rpow_le_one hH0 hH1 (by linarith)
  have hs(i:Fin 3):sqrt (K i).toReal≤sqrt (c i)*v i:=by
    fin_cases i
    · change sqrt ((ENNReal.ofReal (3*A^2*2^(2*(β/100))*Λ^(-SHE.rho β)*
          PastReferenceBandConstants.covariance Q κ M k Babs (β/100))*ENNReal.ofReal (m^2)).toReal)≤_
      have he:3*A^2*2^(2*(β/100))*Λ^(-SHE.rho β)*
          PastReferenceBandConstants.covariance Q κ M k Babs (β/100)=c 0*Λ^(-SHE.rho β):=by
        dsimp [c,rawConstants];ring
      rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg (hc 0) (rpow_nonneg hΛ0.le _)),ENNReal.toReal_ofReal (sq_nonneg m),
        sqrt_mul (mul_nonneg (hc 0) (rpow_nonneg hΛ0.le _)),sqrt_sq hm,
        sqrt_mul (hc 0),sqrt_rpow hΛ0.le]
      dsimp [v,linear]
      nlinarith
    · change sqrt ((ENNReal.ofReal (3*A^2*2^(2*(β/100))*Λ^(-SHE.rho β)*
          PastReferenceBandConstants.baseline Q κ M k Babs (β/100))*ENNReal.ofReal (m^2)).toReal)≤_
      have he:3*A^2*2^(2*(β/100))*Λ^(-SHE.rho β)*
          PastReferenceBandConstants.baseline Q κ M k Babs (β/100)=c 1*Λ^(-SHE.rho β):=by
        dsimp [c,rawConstants];ring
      rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg (hc 1) (rpow_nonneg hΛ0.le _)),ENNReal.toReal_ofReal (sq_nonneg m),
        sqrt_mul (mul_nonneg (hc 1) (rpow_nonneg hΛ0.le _)),sqrt_sq hm,
        sqrt_mul (hc 1),sqrt_rpow hΛ0.le]
      dsimp [v,linear]
      nlinarith
    · change sqrt ((ENNReal.ofReal (3*A^2*2^(2*(β/100))*Λ^(-2*(β/100))*
          PastReferenceBandConstants.mean Q κ M k p B0 (SHE.rho β) χ (β/100) (β/100))*
          (ENNReal.ofReal (m^2)^χ*ENNReal.ofReal H^(1-χ))).toReal)≤_
      have he:3*A^2*2^(2*(β/100))*Λ^(-2*(β/100))*
          PastReferenceBandConstants.mean Q κ M k p B0 (SHE.rho β) χ (β/100) (β/100)=
          c 2*Λ^(-2*(β/100)):=by dsimp [c,rawConstants,χ];ring
      rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg (hc 2) (rpow_nonneg hΛ0.le _)),ENNReal.toReal_mul,
        ←ENNReal.toReal_rpow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal (sq_nonneg m),
        ENNReal.toReal_ofReal hH0,power_sq hm]
      have hl:(c 2*Λ^(-2*(β/100)))*((m^χ)^2*H^(1-χ))≤
          (c 2*Λ^(-2*(β/100)))*(m^χ)^2:=by
        nlinarith only [hHp1,mul_nonneg (mul_nonneg (hc 2) (rpow_nonneg hΛ0.le (-2*(β/100)))) (sq_nonneg (m^χ))]
      apply (sqrt_le_sqrt hl).trans_eq
      rw [sqrt_mul (mul_nonneg (hc 2) (rpow_nonneg hΛ0.le _)),sqrt_sq (rpow_nonneg hm χ),
        sqrt_mul (hc 2),sqrt_rpow hΛ0.le]
      rw [show -2*(β/100)/2=-β/100 by ring]
      norm_num [v]
      ring
  let d:Fin 3→ℝ:=fun i=>sqrt (c i)*StateBands.geometricConstant (degrees β k i/2)
  have hd(i:Fin 3):0≤d i:=mul_nonneg (sqrt_nonneg _) (geometric_nonneg (by
    exact (div_pos (degrees_pos hβ hβsmall k i) (by norm_num)).le))
  have hv(i:Fin 3):0≤v i:=by fin_cases i <;> simp only [v] <;> dsimp [linear] <;> positivity
  have hb:(∑i:Fin 3,sqrt (K i).toReal*StateBands.geometricConstant (degrees β k i/2)*R^(-(degrees β k i/2)))≤
      ∑i:Fin 3,d i*v i:=by
    apply Finset.sum_le_sum
    intro i _
    have hr:R^(-(degrees β k i/2))≤1:=rpow_le_one_of_one_le_of_nonpos hR (by
      linarith only [degrees_pos hβ hβsmall k i])
    have hg:=geometric_nonneg (q:=degrees β k i/2) (by positivity [degrees_pos hβ hβsmall k i])
    have h1:=mul_le_mul_of_nonneg_right (hs i) hg
    have h2:=mul_le_mul_of_nonneg_left hr (mul_nonneg (sqrt_nonneg (K i).toReal) hg)
    dsimp [d]
    nlinarith only [h1,h2]
  apply hb.trans
  change (∑i:Fin 3,d i*v i)≤(1+∑i:Fin 3,d i)*(linear β Λ*m+Λ^(-β/100)*m^χ)
  simp only [Fin.sum_univ_three]
  have hc0:=hd 0
  have hc1:=hd 1
  have hc2:=hd 2
  have hv0:=hv 0
  have hv2:=hv 2
  simp only [v,Fin.reduceEq,ite_false,ite_true] at *
  nlinarith only [hc0,hc1,hc2,hv0,hv2,
    mul_nonneg (add_nonneg (by norm_num:(0:ℝ)≤1) hc2) hv0,
    mul_nonneg (add_nonneg (add_nonneg (by norm_num:(0:ℝ)≤1) hc0) hc1) hv2]

/-- The reference linear slot is small after the actual energy scaling,
without spending any additional band decay. -/
theorem scaled_linear{β Λ:ℝ}(hΛ:0<Λ):energyScale β Λ*linear β Λ=Λ^(-(1/4:ℝ)):=by
  unfold energyScale linear
  rw [←rpow_add hΛ]
  congr 1
  ring

theorem linear_limit(β:ℝ):Tendsto (fun Λ=>energyScale β Λ*linear β Λ) atTop (𝓝 0):=by
  apply (tendsto_rpow_neg_atTop (by norm_num:(0:ℝ)<1/4)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Λ hΛ
  exact (scaled_linear (β:=β) hΛ).symm
end SHE.NativeReferenceMasterCoefficient
