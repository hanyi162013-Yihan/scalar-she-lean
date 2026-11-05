module
public import SHE.NativeGammaClock
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeGammaDamping
open MeasureTheory PredictableL2
open scoped NNReal
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Λ:ℝ) (v b:ℝ≥0)
def value (p:ℝ≥0×Ω):ℝ:=Real.exp (-Λ*NativeGammaClock.age v b p)
theorem measurable :Measurable[𝓕.predictable] (value (Ω:=Ω) Λ v b):=
  ((NativeGammaClock.age_measurable 𝓕 v b).const_mul (-Λ)).exp
theorem nonneg (p:ℝ≥0×Ω):0≤value Λ v b p:=(Real.exp_pos _).le
theorem le_one (hΛ:0≤Λ) (p:ℝ≥0×Ω):value Λ v b p≤1:=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (NativeGammaClock.age_pos v b p).le)
theorem on_window (p:ℝ≥0×Ω) (hp:p∈NativeGammaClock.window v b):
    value Λ v b p=Real.exp (-Λ*((b:ℝ)-(p.1:ℝ))):=by
  simp only [value,NativeGammaClock.age,ite_eq_left hp]
end SHE.NativeGammaDamping
