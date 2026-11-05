module
public import SHE.NativeGammaSingleFourier
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeGammaPairedFourier
open Set MeasureTheory AddCircle StoppedFourier FiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {P:Type*}[MeasurableSpace P]
variable {Λ ρ m U:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(hρhalf:ρ<1/2)(hm:0<m)
variable (B:ℝ)(g:Fin 6→P×HeatCircle→ℂ)(hgm:∀i,Measurable (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)
variable (t:P→ℝ)(htm:Measurable t)(ht:∀p,0<t p)(ht1:∀p,t p≤1)

include B hgm hg ht in
theorem term_integrable (i:Fin 6)(c:P→EllipticField m U)(p:P)(k:HaarNode)(l:ℤ):
    Integrable (fun x:HeatCircle=>fourier (-l) x*
      (g i (p,x)*(NativeObservationCovariance.row hm (c p) (t p) 0 x k:ℂ))) haarAddCircle:=by
  let f:=CircleNormalization.push (globalHaarColumn k (c p).1)
  let W:=NativeMultiplierTrace.multiplier (NativeRandomRows.nativeRow (g i) p) B
    (NativeMultiplierColumnFields.row_bound (hgm i) (fun _=>B) (hg i) p)
    (circleHeatOperator (t p) (ht p).le f)
  have he:=NativeHeatRowsForward.multiplier_row_ae (T:=t p) (q:=0) hm (c p) (ht p)
    (hgm i) (fun _=>B) (hg i) p k
  simp only [sub_zero] at he
  have hi:=((Lp.memLp W).integrable (by norm_num : (1:ℝ≥0∞)≤2)).bdd_mul
    (fourier (-l)).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (fun x=>show ‖fourier (-l) x‖≤(1:ℝ) by simp [fourier_apply]))
  apply hi.congr
  filter_upwards [he] with x hx
  change fourier (-l) x*W x=_
  rw [show W x=g i (p,x)*(NativeObservationCovariance.row hm (c p) (t p) 0 x k:ℂ) from hx]

/-- The complete actual paired Hilbert column is the Fourier average
of the complete physical signed row, retaining all four endpoint terms. -/
theorem coefficient (c0 c1 r0 r1:P→EllipticField m U)(p:P)(k:HaarNode)(l:ℤ):
    NativeFourierNoiseRows.coefficient l
      (NativePairedColumnFields.paired hΛ hρ hρhalf hm B g hgm hg t htm ht ht1 c0 c1 r0 r1 p k)=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*(
          g 0 (p,x)*(NativeObservationCovariance.row hm (c0 p) (t p) 0 x k:ℂ)-
          g 3 (p,x)*(NativeObservationCovariance.row hm (r0 p) (t p) 0 x k:ℂ)-
          g 2 (p,x)*(NativeObservationCovariance.row hm (c1 p) (t p) 0 x k:ℂ)+
          g 5 (p,x)*(NativeObservationCovariance.row hm (r1 p) (t p) 0 x k:ℂ)) ∂haarAddCircle:=by
  have hi0:=term_integrable hm B g hgm hg t ht 0 c0 p k l
  have hi3:=term_integrable hm B g hgm hg t ht 3 r0 p k l
  have hi2:=term_integrable hm B g hgm hg t ht 2 c1 p k l
  have hi5:=term_integrable hm B g hgm hg t ht 5 r1 p k l
  simp only [NativePairedColumnFields.paired,lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply,
    map_add,map_sub,NativeGammaSingleFourier.coefficient]
  simp_rw [mul_add,mul_sub]
  have he3:=integral_sub hi0 hi3
  have he2:=integral_sub (hi0.sub hi3) hi2
  have he5:=integral_add ((hi0.sub hi3).sub hi2) hi5
  simp only [Pi.sub_apply,Pi.add_apply] at he3 he2 he5
  rw [he5,he2,he3]
  ring
end SHE.NativeGammaPairedFourier
