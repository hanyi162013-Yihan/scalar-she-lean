module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.GammaEnvelopeIntegral
open MeasureTheory
open scoped ENNReal
variable {X:Type*} [MeasurableSpace X]
/-- Exact integral of the six genuinely measurable dominating fields.
This does not assert measurability of parameterwise reference versions. -/
theorem identity (ν:Measure X) (s f c v r:X→ℝ≥0∞)
    (hs:Measurable s)(hf:Measurable f)(hc:Measurable c)(hv:Measurable v)(hr:Measurable r)
    (Cs Cf K:ℝ≥0∞):
    (∫⁻x,6*(Cs*s x+Cf*f x+K*(c x+v x+r x+v x)) ∂ν)=
      6*(Cs*(∫⁻x,s x ∂ν)+Cf*(∫⁻x,f x ∂ν)+K*((∫⁻x,c x ∂ν)+(∫⁻x,v x ∂ν)+
        (∫⁻x,r x ∂ν)+(∫⁻x,v x ∂ν))):=by
  have hS:=hs.const_mul Cs
  have hF:=hf.const_mul Cf
  have hSF:Measurable (fun x=>Cs*s x+Cf*f x):=hS.add hF
  have hcv:Measurable (fun x=>c x+v x):=hc.add hv
  have hcvr:Measurable (fun x=>c x+v x+r x):=hcv.add hr
  have hrow:Measurable (fun x=>c x+v x+r x+v x):=hcvr.add hv
  have hK:=hrow.const_mul K
  have hsum:Measurable (fun x=>Cs*s x+Cf*f x+K*(c x+v x+r x+v x)):=hSF.add hK
  rw [lintegral_const_mul _ hsum,lintegral_add_left hSF,lintegral_add_left hS,
    lintegral_const_mul _ hs,lintegral_const_mul _ hf,lintegral_const_mul _ hrow,
    lintegral_add_left hcvr,lintegral_add_left hcv,lintegral_add_left hc]

/-- Proven section caps may be inserted after the exact measurable
outer sum; no interchange of uncountably many exceptional sets occurs. -/
theorem bound (ν:Measure X) (s f c v r:X→ℝ≥0∞)
    (hs:Measurable s)(hf:Measurable f)(hc:Measurable c)(hv:Measurable v)(hr:Measurable r)
    (Cs Cf K S F C V R:ℝ≥0∞)
    (hS:(∫⁻x,s x ∂ν)≤S)(hF:(∫⁻x,f x ∂ν)≤F)(hC:(∫⁻x,c x ∂ν)≤C)
    (hV:(∫⁻x,v x ∂ν)≤V)(hR:(∫⁻x,r x ∂ν)≤R):
    (∫⁻x,6*(Cs*s x+Cf*f x+K*(c x+v x+r x+v x)) ∂ν)≤
      6*(Cs*S+Cf*F+K*(C+V+R+V)):=by
  rw [identity ν s f c v r hs hf hc hv hr Cs Cf K]
  gcongr
end SHE.GammaEnvelopeIntegral
