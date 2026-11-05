module
public import SHE.RemainderBandSpans
public import SHE.ScalarDyadicBands
public import SHE.StateBands
public import SHE.Parameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SHE.GammaDyadicWindowScale
open Real

def alpha (β ρ:ℝ):ℝ:=β+2*ρ
def degree (β ρ:ℝ):ℝ:=alpha β ρ-3*β*(1-β)/4

theorem degree_eq (β:ℝ):degree β (SHE.rho β)=SHE.qGamma β:=by
  unfold degree alpha SHE.qGamma SHE.alpha SHE.k
  ring

theorem radius_power (j:ℕ)(p:ℝ):
    CompactMollifier.radius j^p=((2:ℝ)^j)^(-p):=by
  simpa using ScalarDyadicBands.radius_frequency j p 0

theorem radius_inverse (j:ℕ):CompactMollifier.radius j=((2:ℝ)^j)⁻¹:=by
  simp only [CompactMollifier.radius,inv_pow]

/-- The actual dyadic window h_j=(2^j)^(-3 beta), without replacing it
by a damping-dependent proxy, gives exactly the printed Gamma degree. -/
theorem initial_window_power (β ρ:ℝ)(j:ℕ):
    CompactMollifier.radius j^(2*β+4*ρ)*
      (RemainderBandSpans.span β j:ℝ)^((β-1)/2)=
      ((2:ℝ)^j)^(-2*degree β ρ):=by
  rw [radius_power]
  change ((2:ℝ)^j)^(-(2*β+4*ρ))*
    (((2:ℝ)^j)^(-3*β))^((β-1)/2)=_
  rw [←Real.rpow_mul (by positivity),←Real.rpow_add (by positivity)]
  congr 1
  unfold degree alpha
  ring

theorem clipped_square {x:ℝ}(hx:0≤x):
    (min 1 x)^2=min 1 (x^2):=by
  by_cases h:x≤1
  · rw [min_eq_right h,min_eq_right (by nlinarith)]
  · have hh:1≤x:=(lt_of_not_ge h).le
    rw [min_eq_left hh,min_eq_left (by nlinarith)]
    norm_num

/-- Exact unsquared Gamma bound at a positive dyadic frequency. This
retains both linear inputs and the clipped nonlinear root term. -/
theorem norm_of_squared {E:Type*}[NormedAddCommGroup E]
    {C β ρ K m:ℝ}(hC:0≤C)(hK:0≤K)(hm:0≤m)(j:ℕ)(x:E)
    (hbound:‖x‖^2≤C*(CompactMollifier.radius j^(2*β)*K^2+
      CompactMollifier.radius j^(2*β+4*ρ)*
        ((RemainderBandSpans.span β j:ℝ)^((β-1)/2)*m^2+
          min 1 (m^2/CompactMollifier.radius j^2)))):
    ‖x‖≤sqrt C*(((2:ℝ)^j)^(-β)*K+
      ((2:ℝ)^j)^(-alpha β ρ)*min 1 (m*(2:ℝ)^j)+
      ((2:ℝ)^j)^(-degree β ρ)*m):=by
  let ν:ℝ:=(2:ℝ)^j
  have hν:0<ν:=by dsimp [ν];positivity
  have hclip:m^2/CompactMollifier.radius j^2=(m*ν)^2:=by
    rw [radius_inverse]
    dsimp [ν]
    field_simp
  have hfirst:CompactMollifier.radius j^(2*β)= (ν^(-β))^2:=by
    rw [radius_power,←Real.rpow_mul_natCast hν.le]
    congr 1
    ring
  have hroot:CompactMollifier.radius j^(2*β+4*ρ)= (ν^(-alpha β ρ))^2:=by
    rw [radius_power,←Real.rpow_mul_natCast hν.le]
    congr 1
    unfold alpha
    ring
  have hlinear:CompactMollifier.radius j^(2*β+4*ρ)*
      (RemainderBandSpans.span β j:ℝ)^((β-1)/2)=(ν^(-degree β ρ))^2:=by
    rw [initial_window_power,←Real.rpow_mul_natCast hν.le]
    congr 1
    ring
  have hb:‖x‖^2≤C*((ν^(-β)*K)^2+
      (ν^(-alpha β ρ)*min 1 (m*ν))^2+(ν^(-degree β ρ)*m)^2):=by
    rw [hclip,←clipped_square (mul_nonneg hm hν.le)] at hbound
    calc
      _≤C*(CompactMollifier.radius j^(2*β)*K^2+
          CompactMollifier.radius j^(2*β+4*ρ)*
            ((RemainderBandSpans.span β j:ℝ)^((β-1)/2)*m^2+(min 1 (m*ν))^2)):=hbound
      _=_:=by
        congr 1
        rw [mul_add,←mul_assoc,hlinear,hfirst,hroot]
        ring
  have hu:0≤ν^(-β)*K:=by positivity
  have hv:0≤ν^(-alpha β ρ)*min 1 (m*ν):=by positivity
  have hw:0≤ν^(-degree β ρ)*m:=by positivity
  have hsum:(ν^(-β)*K)^2+(ν^(-alpha β ρ)*min 1 (m*ν))^2+
      (ν^(-degree β ρ)*m)^2≤
      (ν^(-β)*K+ν^(-alpha β ρ)*min 1 (m*ν)+ν^(-degree β ρ)*m)^2:=by
    nlinarith [mul_nonneg hu hv,mul_nonneg hu hw,mul_nonneg hv hw]
  have hs:‖x‖^2≤(sqrt C*(ν^(-β)*K+ν^(-alpha β ρ)*min 1 (m*ν)+ν^(-degree β ρ)*m))^2:=by
    rw [mul_pow,sq_sqrt hC]
    exact hb.trans (mul_le_mul_of_nonneg_left hsum hC)
  have hright:0≤sqrt C*(ν^(-β)*K+ν^(-alpha β ρ)*min 1 (m*ν)+ν^(-degree β ρ)*m):=by positivity
  change ‖x‖≤sqrt C*(ν^(-β)*K+ν^(-alpha β ρ)*min 1 (m*ν)+ν^(-degree β ρ)*m)
  nlinarith [norm_nonneg x]
end SHE.GammaDyadicWindowScale
