module

public import SHE.NativePairedGammaProcess
public import SHE.NativeHeatRowsForward
public import SHE.NativeBesselReal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativePairedColumnsReal
open MeasureTheory Set AddCircle StoppedFourier FiniteHaar NativeMultiplierHilbertColumns
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {P:Type*} [MeasurableSpace P]
variable {Λ ρ m U:ℝ} (hΛ:1≤Λ) (hρ:0≤ρ) (hρhalf:ρ<1/2) (hm:0<m)
variable (B:ℝ) (g:Fin 6→P×HeatCircle→ℂ) (hgm:∀i,Measurable (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B) (hr:∀i p x,(g i (p,x)).im=0)
variable (t:P→ℝ) (htm:Measurable t) (ht:∀p,0<t p) (ht1:∀p,t p≤1)

include hr in
theorem single_real (i:Fin 6) (c:P→EllipticField m U) (p:P) (q:HaarNode):
    ∀ᵐx∂haarAddCircle,(NativePairedColumnFields.single hΛ hρ hρhalf hm B g hgm hg t htm ht ht1 i c p q x).im=0:=by
  change ∀ᵐx∂haarAddCircle,(NativeMultiplierColumnFields.column hΛ hρ (g i) t hm c p q x).im=0
  rw [NativeMultiplierColumnFields.column,NativeMultiplierColumnFields.operator_eq (hgm i) (fun _=>B) (hg i) htm ht]
  apply NativeBesselReal.bessel_real
  have he:=NativeHeatRowsForward.multiplier_row_ae (T:=t p) (q:=0) hm (c p) (ht p) (hgm i) (fun _=>B) (hg i) p q
  simp only [sub_zero] at he
  filter_upwards [he] with x hx
  rw [hx]
  simp only [Complex.mul_im,hr i p x,Complex.ofReal_im,mul_zero,zero_mul,add_zero]

theorem real_add (f h:CircleL2) (hf:∀ᵐx∂haarAddCircle,(f x).im=0) (hh:∀ᵐx∂haarAddCircle,(h x).im=0):
    ∀ᵐx∂haarAddCircle,((f+h) x).im=0:=by
  filter_upwards [hf,hh,Lp.coeFn_add f h] with x hf hh hx
  rw [hx]
  simp only [Pi.add_apply,Complex.add_im,hf,hh,add_zero]

theorem real_sub (f h:CircleL2) (hf:∀ᵐx∂haarAddCircle,(f x).im=0) (hh:∀ᵐx∂haarAddCircle,(h x).im=0):
    ∀ᵐx∂haarAddCircle,((f-h) x).im=0:=by
  filter_upwards [hf,hh,Lp.coeFn_sub f h] with x hf hh hx
  rw [hx]
  simp only [Pi.sub_apply,Complex.sub_im,hf,hh,sub_self]

include hr in
/-- All four original paired columns remain in the real physical
subspace, including the massive native Bessel multiplier. -/
theorem paired_real (c0 c1 r0 r1:P→EllipticField m U) (p:P) (q:HaarNode):
    ∀ᵐx∂haarAddCircle,(NativePairedColumnFields.paired hΛ hρ hρhalf hm B g hgm hg t htm ht ht1 c0 c1 r0 r1 p q x).im=0:=by
  simp only [NativePairedColumnFields.paired,lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply]
  apply real_add
  · apply real_sub
    · apply real_sub
      · exact single_real hΛ hρ hρhalf hm B g hgm hg hr t htm ht ht1 0 c0 p q
      · exact single_real hΛ hρ hρhalf hm B g hgm hg hr t htm ht ht1 3 r0 p q
    · exact single_real hΛ hρ hρhalf hm B g hgm hg hr t htm ht ht1 2 c1 p q
  · exact single_real hΛ hρ hρhalf hm B g hgm hg hr t htm ht ht1 5 r1 p q

end SHE.NativePairedColumnsReal
