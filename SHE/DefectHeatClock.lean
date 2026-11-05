module

public import SHE.DefectCombinedTime
public import SHE.HeatSpanSignedHaarTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace SHE.DefectHeatClock
open Real

def traceAge (θ Λ ρ w:ℝ):ℝ:=sqrt w*
  (Λ^ρ*(θ*w)^(-(1/2:ℝ))+(θ*w)^(-(1/2:ℝ)-ρ))

/-- The real native heat-span rank factor cancels the heat trace's
one-half age singularity exactly. -/
theorem traceAge_eq {θ Λ ρ w:ℝ}(hθ:0<θ)(hw:0<w):
    traceAge θ Λ ρ w=θ^(-(1/2:ℝ))*Λ^ρ+θ^(-(1/2:ℝ)-ρ)*w^(-ρ):=by
  have h1:sqrt w*(θ*w)^(-(1/2:ℝ))=θ^(-(1/2:ℝ)):=by
    rw [sqrt_eq_rpow,mul_rpow hθ.le hw.le]
    calc
      _=θ^(-(1/2:ℝ))*(w^(1/2:ℝ)*w^(-(1/2:ℝ))):=by ring
      _=_:=by rw [←rpow_add hw];norm_num
  have h2:sqrt w*(θ*w)^(-(1/2:ℝ)-ρ)=θ^(-(1/2:ℝ)-ρ)*w^(-ρ):=by
    rw [sqrt_eq_rpow,mul_rpow hθ.le hw.le]
    calc
      _=θ^(-(1/2:ℝ)-ρ)*(w^(1/2:ℝ)*w^(-(1/2:ℝ)-ρ)):=by ring
      _=_:=by rw [←rpow_add hw];congr 1 <;>ring
  calc
    _=Λ^ρ*(sqrt w*(θ*w)^(-(1/2:ℝ)))+sqrt w*(θ*w)^(-(1/2:ℝ)-ρ):=by
      unfold traceAge;ring
    _=_:=by rw [h1,h2];ring

/-- The actual negative-output mass cancels the positive damping
power, leaving the precise signed-input endpoint correction. -/
theorem normalized_trace {θ Λ ρ w:ℝ}(hθ:0<θ)(hΛ:0<Λ)(hw:0<w):
    Λ^(-ρ)*traceAge θ Λ ρ w=
      θ^(-(1/2:ℝ))+θ^(-(1/2:ℝ)-ρ)*Λ^(-ρ)*w^(-ρ):=by
  rw [traceAge_eq hθ hw,mul_add]
  have hp:Λ^(-ρ)*Λ^ρ=1:=by rw [←rpow_add hΛ];norm_num
  calc
    _=θ^(-(1/2:ℝ))*(Λ^(-ρ)*Λ^ρ)+θ^(-(1/2:ℝ)-ρ)*Λ^(-ρ)*w^(-ρ):=by ring
    _=_:=by rw [hp];ring

theorem normalized_trace_bound {θ Λ ρ w:ℝ}(hθ:0<θ)(hΛ:0<Λ)(hw:0<w):
    Λ^(-ρ)*traceAge θ Λ ρ w≤
      max (θ^(-(1/2:ℝ))) (θ^(-(1/2:ℝ)-ρ))*(1+Λ^(-ρ)*w^(-ρ)):=by
  rw [normalized_trace hθ hΛ hw,mul_add,mul_one]
  apply add_le_add (le_max_left _ _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right (θ^(-(1/2:ℝ))) (θ^(-(1/2:ℝ)-ρ)))
      (rpow_nonneg hΛ.le (-ρ))) (rpow_nonneg hw.le (-ρ))

/-- The exact RMS form feeding the new-time kernel: the negative
output gain is retained before taking the square root. -/
theorem normalized_sqrt_trace {θ Λ ρ w:ℝ}(hθ:0<θ)(hΛ:0<Λ)(hw:0<w):
    Λ^(-ρ/2)*sqrt (traceAge θ Λ ρ w)≤
      sqrt (max (θ^(-(1/2:ℝ))) (θ^(-(1/2:ℝ)-ρ)))*
        (1+Λ^(-ρ/2)*w^(-ρ/2)):=by
  let C:=max (θ^(-(1/2:ℝ))) (θ^(-(1/2:ℝ)-ρ))
  have hC:0≤C:=(rpow_nonneg hθ.le _).trans (le_max_left _ _)
  have hA:0≤traceAge θ Λ ρ w:=by
    unfold traceAge
    exact mul_nonneg (sqrt_nonneg _) (add_nonneg
      (mul_nonneg (rpow_nonneg hΛ.le _) (rpow_nonneg (mul_pos hθ hw).le _))
      (rpow_nonneg (mul_pos hθ hw).le _))
  have hL:(Λ^(-ρ/2))^2=Λ^(-ρ):=by
    rw [←rpow_mul_natCast hΛ.le]
    congr 1
    ring
  have hW:(w^(-ρ/2))^2=w^(-ρ):=by
    rw [←rpow_mul_natCast hw.le]
    congr 1
    ring
  have hp:0≤Λ^(-ρ/2)*w^(-ρ/2):=mul_nonneg (rpow_nonneg hΛ.le _) (rpow_nonneg hw.le _)
  apply (sq_le_sq₀ (mul_nonneg (rpow_nonneg hΛ.le _) (sqrt_nonneg _))
    (mul_nonneg (sqrt_nonneg _) (by positivity))).mp
  rw [mul_pow,sq_sqrt hA,hL,mul_pow,sq_sqrt hC]
  calc
    _≤C*(1+Λ^(-ρ)*w^(-ρ)):=normalized_trace_bound hθ hΛ hw
    _=C*(1+(Λ^(-ρ/2)*w^(-ρ/2))^2):=by rw [mul_pow,hL,hW]
    _≤C*(1+Λ^(-ρ/2)*w^(-ρ/2))^2:=by nlinarith

end SHE.DefectHeatClock
