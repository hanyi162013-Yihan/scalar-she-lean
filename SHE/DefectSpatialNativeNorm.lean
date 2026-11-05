module
public import SHE.DefectSpatialAverage
public import SHE.NativeBesselFieldAE
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
namespace SHE.DefectSpatialNativeNorm
open Set MeasureTheory Real AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable {W P:Type*}[MeasurableSpace W][MeasurableSpace P]

/-- The positive-parent root average has its actual native norm bound
and genuine spatial L2 section, from the sharp scaled root estimates.
Every current/random parameter remains inside the given spatial field. -/
theorem norm_le (ν:Measure W)[IsProbabilityMeasure ν]
    (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)
    (F:AddCircle (1:ℝ)×W→ℝ)(hF:Measurable F)
    (H:W→ℝ)(hH:Measurable H)(hHi:Integrable H ν)(hH0:∀w,0≤H w)
    (A:P×HeatCircle→ℝ)(hA:Measurable A)(p:P)
    (he:∀ᵐx:AddCircle (1:ℝ)∂haarAddCircle,
      A (p,CircleNormalization.scale 1 (2*Real.pi) x)=∫w,F (x,w) ∂ν)
    {L:ℝ}(hL:0≤L)
    (hi:∀ᵐw∂ν,Integrable (fun x:AddCircle (1:ℝ)=>|F (x,w)|^2) haarAddCircle)
    (hb:∀ᵐw∂ν,Λ^(-ρ/2)*sqrt (∫x:AddCircle (1:ℝ),|F (x,w)|^2 ∂haarAddCircle)≤L*H w):
    MemLp (fun x:HeatCircle=>(A (p,x):ℂ)) 2 haarAddCircle ∧
      ‖NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z:P×HeatCircle=>(A z:ℂ)) p‖≤
        L*(∫w,H w ∂ν):=by
  have hΛp:0<Λ:=zero_lt_one.trans_le hΛ
  have hcancel:Λ^(ρ/2)*Λ^(-ρ/2)=1:=by
    rw [←rpow_add hΛp,show ρ/2+-ρ/2=0 by ring,rpow_zero]
  have hb2:∀ᵐw∂ν,(∫x:AddCircle (1:ℝ),|F (x,w)|^2 ∂haarAddCircle)≤
      ((Λ^(ρ/2)*L)^2)*(H w)^2:=by
    filter_upwards [hb] with w hw
    let I:ℝ:=∫x:AddCircle (1:ℝ),|F (x,w)|^2 ∂haarAddCircle
    have hI:0≤I:=integral_nonneg (fun _=>sq_nonneg _)
    have hs:sqrt I≤(Λ^(ρ/2)*L)*H w:=by
      calc
        sqrt I=(Λ^(ρ/2)*Λ^(-ρ/2))*sqrt I:=by rw [hcancel,one_mul]
        _=Λ^(ρ/2)*(Λ^(-ρ/2)*sqrt I):=by ring
        _≤Λ^(ρ/2)*(L*H w):=mul_le_mul_of_nonneg_left hw (rpow_nonneg hΛp.le _)
        _=_:=by ring
    simpa only [sq_sqrt hI,mul_pow] using pow_le_pow_left₀ (sqrt_nonneg I) hs 2
  have hAp:Measurable (fun x:HeatCircle=>A (p,x)):=hA.comp (measurable_const.prodMk measurable_id)
  have h:=DefectSpatialAverage.energy ν Λ ρ hΛ hρ F hF H hH hHi hH0
    (fun x=>A (p,x)) hAp he (sq_nonneg _) hi hb2
  have hAc:Measurable (fun z:P×HeatCircle=>(A z:ℂ)):=Complex.continuous_ofReal.measurable.comp hA
  have hc:=NativeBesselFieldAE.coefficients Λ ρ hΛ hρ (fun z:P×HeatCircle=>(A z:ℂ)) hAc p
    ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle _ hAc p).mp h.1)
  have heN:‖NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z:P×HeatCircle=>(A z:ℂ)) p‖^2=
      NativeFourierAverage.scalarEnergy Λ ρ (fun x:HeatCircle=>(A (p,x):ℂ)):=
    (NativeFourierAverage.energy_of_identified Λ ρ hΛ _ _ hc).2.symm
  have hpow:Λ^(-ρ)*(Λ^(ρ/2)*L)^2=L^2:=by
    rw [mul_pow,←rpow_mul_natCast hΛp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (ρ/2)*(2:ℝ)=ρ by ring]
    rw [←mul_assoc,←rpow_add hΛp,neg_add_cancel,rpow_zero,one_mul]
  refine ⟨h.1,?_⟩
  have hs:‖NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z:P×HeatCircle=>(A z:ℂ)) p‖^2≤
      (L*(∫w,H w ∂ν))^2:=by
    rw [heN,mul_pow]
    exact h.2.trans_eq (by rw [hpow])
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (integral_nonneg hH0))).mp hs
end SHE.DefectSpatialNativeNorm
