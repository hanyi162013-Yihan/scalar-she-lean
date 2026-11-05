module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ComplexRealification
open MeasureTheory
def value (z:ℂ):ℂ:=(z.re:ℝ)
theorem measurable:Measurable value:=
  Complex.continuous_ofReal.measurable.comp Complex.continuous_re.measurable
@[simp] theorem im (z:ℂ):(value z).im=0:=rfl
theorem norm_le (z:ℂ):‖value z‖≤‖z‖:=by
  simpa only [value,Complex.norm_real,Real.norm_eq_abs] using Complex.abs_re_le_norm z
theorem eq {z:ℂ}(hz:z.im=0):value z=z:=by
  apply Complex.ext
  · rfl
  · exact hz.symm
end SHE.ComplexRealification
