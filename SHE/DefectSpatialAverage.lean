module

public import SHE.WeightedSpatialMoments
public import SHE.NativeUnitRootEnergy
public import SHE.NativeBesselSectionEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SHE.DefectSpatialAverage
open Set MeasureTheory Real AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- True positive-parent averaging retains its L1 mass, then gives
spatial L2 membership and the native massive Bessel bound. The square
is taken after the old-space integral. -/
theorem energy {W:Type*}[MeasurableSpace W](ν:Measure W)[IsProbabilityMeasure ν]
    (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)
    (F:AddCircle (1:ℝ)×W→ℝ)(hF:Measurable F)
    (H:W→ℝ)(hH:Measurable H)(hHi:Integrable H ν)(hH0:∀w,0≤H w)
    (A:HeatCircle→ℝ)(hA:Measurable A)
    (he:∀ᵐx:AddCircle (1:ℝ)∂haarAddCircle,
      A (CircleNormalization.scale 1 (2*Real.pi) x)=∫w,F (x,w) ∂ν)
    {B:ℝ}(hB:0≤B)
    (hi:∀ᵐw∂ν,Integrable (fun x:AddCircle (1:ℝ)=>|F (x,w)|^2) haarAddCircle)
    (hb:∀ᵐw∂ν,(∫x:AddCircle (1:ℝ),|F (x,w)|^2 ∂haarAddCircle)≤B*(H w)^2):
    MemLp (fun x:HeatCircle=>(A x:ℂ)) 2 haarAddCircle ∧
      NativeFourierAverage.scalarEnergy Λ ρ (fun x:HeatCircle=>(A x:ℂ))≤
        Λ^(-ρ)*B*(∫w,H w ∂ν)^2:=by
  have hJ:=WeightedSpatialMoments.nonnegative_envelope
    (haarAddCircle:Measure (AddCircle (1:ℝ))) ν F hF H hH hHi hH0 1 zero_lt_one B hB
    (by simpa only [Nat.mul_one] using hi) (by simpa only [Nat.mul_one] using hb)
  have hp:(fun x:AddCircle (1:ℝ)=>|A (CircleNormalization.scale 1 (2*Real.pi) x)|^2)=ᵐ[haarAddCircle]
      (fun x=>|∫w,F (x,w) ∂ν|^2):=he.mono (fun x hx=>congrArg (fun z:ℝ=>|z|^2) hx)
  have hiA:Integrable (fun x:AddCircle (1:ℝ)=>|A (CircleNormalization.scale 1 (2*Real.pi) x)|^2)
      haarAddCircle:=hJ.1.congr hp.symm
  have hN:=NativeUnitRootEnergy.scalar Λ ρ hΛ hρ A hA hiA
  refine ⟨hN.1,hN.2.trans ?_⟩
  rw [integral_congr_ae hp]
  have hh:=mul_le_mul_of_nonneg_left hJ.2 (rpow_nonneg (zero_le_one.trans hΛ) (-ρ))
  simpa only [Nat.mul_one,mul_assoc] using hh

end SHE.DefectSpatialAverage
