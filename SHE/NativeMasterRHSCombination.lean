module
public import SHE.ActualReferenceMasterClosure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeMasterRHSCombination
open Real
open scoped BigOperators
theorem rows_nonneg {β Λ m:ℝ}(hΛ:0≤Λ)(hm:0≤m):
    0≤ActualReferenceMasterClosure.rows β Λ m 0 0:=by
  unfold ActualReferenceMasterClosure.rows
  exact Finset.sum_nonneg (fun _ _=>mul_nonneg (rpow_nonneg hΛ _) (rpow_nonneg hm _))

theorem reference_row_le {β Λ m:ℝ}(hΛ:0≤Λ)(hm:0≤m):
    Λ^(-β/100)*m^(ActualReferenceMasterClosure.referenceExponent β)≤
      ActualReferenceMasterClosure.rows β Λ m 0 0:=by
  have hs:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun i:ActualReferenceMasterClosure.Row=>Λ^(-ActualReferenceMasterClosure.damping β i+(0:ℝ))*
      m^(ActualReferenceMasterClosure.exponent β i-(0:ℝ)))
    (fun i _=>mul_nonneg (rpow_nonneg hΛ _) (rpow_nonneg hm _))
    (Finset.mem_univ (none:ActualReferenceMasterClosure.Row))
  simpa only [ActualReferenceMasterClosure.rows,ActualReferenceMasterClosure.damping,
    ActualReferenceMasterClosure.exponent,ActualReferenceMasterClosure.referenceDamping,
    Pi.zero_apply,add_zero,sub_zero,neg_div] using hs

theorem native_row_le {β Λ m:ℝ}(hΛ:0≤Λ)(hm:0≤m):
    m^(SHE.chi β)≤ActualReferenceMasterClosure.rows β Λ m 0 0:=by
  have hs:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun i:ActualReferenceMasterClosure.Row=>Λ^(-ActualReferenceMasterClosure.damping β i+(0:ℝ))*
      m^(ActualReferenceMasterClosure.exponent β i-(0:ℝ)))
    (fun i _=>mul_nonneg (rpow_nonneg hΛ _) (rpow_nonneg hm _))
    (Finset.mem_univ (some MasterRow.native:ActualReferenceMasterClosure.Row))
  simpa only [ActualReferenceMasterClosure.rows,ActualReferenceMasterClosure.damping,
    ActualReferenceMasterClosure.exponent,ZeroNativeDyadicMaster.rowDamping,SHE.rowExponent,
    Pi.zero_apply,add_zero,sub_zero,neg_zero,rpow_zero,one_mul] using hs

theorem combine{β Λ K m Cb Cr Ch ag am ah bm br bh bad err:ℝ}
    (hΛ:0≤Λ)(hK:0≤K)(hm:0≤m)(hCb:0≤Cb)(hCr:0≤Cr)(hCh:0≤Ch)
    (hag:0≤ag)(ham:0≤am)(hah:0≤ah)(hbm:0≤bm)(hbr:0≤br)(hbh:0≤bh)
    (h:K≤Cb*(ag*K+bm*m+ActualReferenceMasterClosure.rows β Λ m 0 0)+
      Cr*(br*m+Λ^(-β/100)*m^(ActualReferenceMasterClosure.referenceExponent β))+
      Ch*(ah*K+bh*m+m^(SHE.chi β)+bad)+am*K+err):
    ActualReferenceMasterClosure.Bound β (1+Cb+Cr+Ch) Λ K m (err+Ch*bad)
      (ag+am+ah) (bm+br+bh) 0 0:=by
  let C:=1+Cb+Cr+Ch
  have hC0:0≤C:=by dsimp [C];linarith
  have hCg:Cb≤C:=by dsimp [C];linarith
  have hCr':Cr≤C:=by dsimp [C];linarith
  have hCh':Ch≤C:=by dsimp [C];linarith
  have hC1:1≤C:=by dsimp [C];linarith
  have hr:=reference_row_le hΛ hm (β:=β)
  have hn:=native_row_le hΛ hm (β:=β)
  have hrows:=rows_nonneg hΛ hm (β:=β)
  have h0:=mul_le_mul_of_nonneg_right hCg (mul_nonneg hag hK)
  have h1:=mul_le_mul_of_nonneg_right hCh' (mul_nonneg hah hK)
  have h2:=mul_le_mul_of_nonneg_right hC1 (mul_nonneg ham hK)
  have h3:=mul_le_mul_of_nonneg_right hCg (mul_nonneg hbm hm)
  have h4:=mul_le_mul_of_nonneg_right hCr' (mul_nonneg hbr hm)
  have h5:=mul_le_mul_of_nonneg_right hCh' (mul_nonneg hbh hm)
  have h6:=mul_le_mul_of_nonneg_left hr hCr
  have h7:=mul_le_mul_of_nonneg_left hn hCh
  have h8:=mul_le_mul_of_nonneg_right (show Cb+Cr+Ch≤C by dsimp [C];linarith) hrows
  unfold ActualReferenceMasterClosure.Bound
  change K≤C*((ag+am+ah)*K+(bm+br+bh)*m+ActualReferenceMasterClosure.rows β Λ m 0 0)+(err+Ch*bad)
  nlinarith only [h,h0,h1,h2,h3,h4,h5,h6,h7,h8]

end SHE.NativeMasterRHSCombination
