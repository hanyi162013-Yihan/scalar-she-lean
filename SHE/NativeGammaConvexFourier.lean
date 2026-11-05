module
public import SHE.NativeGammaPairedFourier
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeGammaConvexFourier
open Set MeasureTheory AddCircle StoppedFourier FiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {P:Type*}[MeasurableSpace P]
variable {Λ ρ m U:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(hρhalf:ρ<1/2)(hm:0<m)
variable (B:ℝ)(g:Fin 6→P×HeatCircle→ℂ)(hgm:∀i,Measurable (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)
variable (t:P→ℝ)(htm:Measurable t)(ht:∀p,0<t p)(ht1:∀p,t p≤1)

def physical (c0 c1 r0 r1:P→EllipticField m U)(p:P)(k:HaarNode)(x:HeatCircle):ℂ:=
  g 0 (p,x)*(NativeObservationCovariance.row hm (c0 p) (t p) 0 x k:ℂ)-
  g 3 (p,x)*(NativeObservationCovariance.row hm (r0 p) (t p) 0 x k:ℂ)-
  g 2 (p,x)*(NativeObservationCovariance.row hm (c1 p) (t p) 0 x k:ℂ)+
  g 5 (p,x)*(NativeObservationCovariance.row hm (r1 p) (t p) 0 x k:ℂ)

include B hgm hg ht in
theorem physical_integrable (c0 c1 r0 r1:P→EllipticField m U)(p:P)(k:HaarNode)(l:ℤ):
    Integrable (fun x:HeatCircle=>fourier (-l) x*physical hm g t c0 c1 r0 r1 p k x) haarAddCircle:=by
  have h0:=NativeGammaPairedFourier.term_integrable hm B g hgm hg t ht 0 c0 p k l
  have h3:=NativeGammaPairedFourier.term_integrable hm B g hgm hg t ht 3 r0 p k l
  have h2:=NativeGammaPairedFourier.term_integrable hm B g hgm hg t ht 2 c1 p k l
  have h5:=NativeGammaPairedFourier.term_integrable hm B g hgm hg t ht 5 r1 p k l
  apply (((h0.sub h3).sub h2).add h5).congr
  filter_upwards with x
  simp only [physical,mul_add,mul_sub,Pi.add_apply,Pi.sub_apply]

/-- The SAME convex original joint noise column has the convex physical
scalar Fourier row INSIDE its integral, for arbitrary predictable weight
values. No averaged diffusion square root is introduced. -/
theorem coefficient (c0 c1 r0 r1:P→EllipticField m U)(p:P)(k:HaarNode)(l:ℤ)(d:ℝ):
    NativeFourierNoiseRows.coefficient l ((d •
      NativePairedColumnFields.paired hΛ hρ hρhalf hm B g hgm hg t htm ht ht1 c0 c1 r0 r1 p+
      (1-d) • NativePairedColumnFields.paired hΛ hρ hρhalf hm B g hgm hg t htm ht ht1 c0 c0 r0 r1 p) k)=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*(d •physical hm g t c0 c1 r0 r1 p k x+
          (1-d) •physical hm g t c0 c0 r0 r1 p k x) ∂haarAddCircle:=by
  have h1:=physical_integrable hm B g hgm hg t ht c0 c1 r0 r1 p k l
  have h0:=physical_integrable hm B g hgm hg t ht c0 c0 r0 r1 p k l
  have he:(∫x:HeatCircle,fourier (-l) x*(d •physical hm g t c0 c1 r0 r1 p k x+
      (1-d) •physical hm g t c0 c0 r0 r1 p k x) ∂haarAddCircle)=
      d •(∫x:HeatCircle,fourier (-l) x*physical hm g t c0 c1 r0 r1 p k x ∂haarAddCircle)+
      (1-d) •(∫x:HeatCircle,fourier (-l) x*physical hm g t c0 c0 r0 r1 p k x ∂haarAddCircle):=by
    simp_rw [mul_add,mul_smul_comm]
    have hadd:=integral_add (Integrable.smul d h1) (Integrable.smul (1-d) h0)
    simp only [Pi.smul_apply] at hadd
    rw [hadd,integral_smul,integral_smul]
  simp only [lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,map_add,map_smul,
    NativeGammaPairedFourier.coefficient]
  change d •(_*_)+(1-d) •(_*_) =_*_
  rw [he]
  simp only [physical,Algebra.smul_def,mul_add]
  ring
end SHE.NativeGammaConvexFourier
