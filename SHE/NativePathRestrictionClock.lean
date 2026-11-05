module
public import SHE.ConditionalContinuousPathExtension
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativePathRestrictionClock
open Set MeasureTheory ContinuousPathRestriction
open scoped NNReal
variable {Ω E:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (v h:ℝ≥0)(U:ℝ≥0→Ω→E)(hc:∀ω,Continuous (fun t=>U t ω))

include hc in
theorem shifted_continuous(ω:Ω):Continuous (fun t:ℝ≥0=>U (v+t) ω):=
  (hc ω).comp (continuous_const.add continuous_id)

/-- The restriction prefix is the original native path stopped at v,
with exactly the same state and clock. -/
theorem past_path(ω:Ω):
    past v h (NativeContinuousPath.path (v+h) U hc ω)=NativeContinuousPath.path v U hc ω:=by
  ext t
  rfl

/-- The future restriction is the literal restarted trajectory t↦U(v+t).
No rescaling, new version, or stochastic restart premise is used. -/
theorem future_path(ω:Ω):
    future v h (NativeContinuousPath.path (v+h) U hc ω)=
      NativeContinuousPath.path h (fun t ω=>U (v+t) ω) (shifted_continuous v U hc) ω:=by
  ext t
  change U (((v:ℝ)+t.val).toNNReal) ω=U (v+t.val.toNNReal) ω
  congr 1
  rw [Real.toNNReal_add v.coe_nonneg t.property.1,Real.toNNReal_coe]
end SHE.NativePathRestrictionClock
