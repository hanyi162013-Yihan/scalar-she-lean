module

public import SHE.FirstWordPowers

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Genuine spatial L² time integration of the clipped root ledger. Coarse
pointwise domination is used only to justify Fubini; the resulting power
comes from the independently supplied sharp section L² estimate. -/
namespace SHE.RootCornerTransfer
open Set MeasureTheory Real ProfileL2

/-- Both endpoint corners are integrated on the actual time-space field.
The coarse domination exponent may differ from the sharp L² exponent. -/
theorem root_corner_minkowski {X:Type*}[MeasurableSpace X](κ:Measure X)[IsProbabilityMeasure κ]
    {ν σ τ h A B:ℝ}(hν:0≤ν)(hσ:-1<σ)(hτ:-1<τ)(hh:0<h)(hA:0≤A)(hB:0≤B)
    (F:ℝ×X→ℝ)(hF:Measurable F)
    (hbound:∀s∈Ioo 0 h,∀x,|F (s,x)|≤B*SHE.rootKernel ν (h-s)*s^τ)
    (hL2:∀s∈Ioo 0 h,normTwo κ (fun x=>F (s,x))≤A*SHE.rootKernel ν (h-s)*s^σ):
    normTwo κ (fun x=>∫s in (0:ℝ)..h,F (s,x))≤
      A*(2*(1+1/(σ+1)))*h^σ*SHE.rootMass ν h:=by
  let μ:=volume.restrict (Ioc 0 h)
  let a:ℝ→ℝ:=fun s=>A*SHE.rootKernel ν (h-s)*s^σ
  let b:ℝ→ℝ:=fun s=>B*SHE.rootKernel ν (h-s)*s^τ
  have hai:Integrable a μ:=by
    have hi:=SHE.root_power_pair_intervalIntegrable hν (show 0<σ+1 by linarith) hh.le
    simp only[add_sub_cancel_right] at hi
    convert! hi.1.const_mul A using 1
    funext s;dsimp[a];ring
  have hbi:Integrable b μ:=by
    have hi:=SHE.root_power_pair_intervalIntegrable hν (show 0<τ+1 by linarith) hh.le
    simp only[add_sub_cancel_right] at hi
    convert! hi.1.const_mul B using 1
    funext s;dsimp[b];ring
  have hgood:∀ᵐs ∂μ,s∈Ioo 0 h:=by
    filter_upwards[ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne h)] with s hs hn
    exact ⟨hs.1,lt_of_le_of_ne hs.2 hn⟩
  have ha0:0≤ᵐ[μ]a:=hgood.mono (fun s hs=>mul_nonneg
    (mul_nonneg hA (SHE.rootKernel_nonneg hν (by linarith[hs.2]))) (rpow_nonneg hs.1.le _))
  have hb0:0≤ᵐ[μ]b:=hgood.mono (fun s hs=>mul_nonneg
    (mul_nonneg hB (SHE.rootKernel_nonneg hν (by linarith[hs.2]))) (rpow_nonneg hs.1.le _))
  have hm:=bounded_minkowski_two hF hai hbi ha0 hb0
    (hgood.mono (fun s hs=>hbound s hs)) (hgood.mono (fun s hs=>hL2 s hs))
  have he:=SHE.root_power_convolution_le hν (show 0<σ+1 by linarith) hh
  simp only[add_sub_cancel_right] at he
  have he':(∫s in (0:ℝ)..h,SHE.rootKernel ν (h-s)*s^σ)≤
      (2*(1+1/(σ+1)))*h^σ*SHE.rootMass ν h:=by
    convert! he using 1
    congr 1;funext s;ring
  have hval:(∫s,a s ∂μ)=A*(∫s in (0:ℝ)..h,SHE.rootKernel ν (h-s)*s^σ):=by
    rw[intervalIntegral.integral_of_le hh.le,←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun s=>by dsimp[a];ring)
  have hleft:(fun x=>∫s,F (s,x) ∂μ)=(fun x=>∫s in (0:ℝ)..h,F (s,x)):=by
    funext x;rw[intervalIntegral.integral_of_le hh.le]
  rw[hleft,hval] at hm
  convert! hm.trans (mul_le_mul_of_nonneg_left he' hA) using 1
  ring

end SHE.RootCornerTransfer
