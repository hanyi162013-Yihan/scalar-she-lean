module

public import SHE.HeatMarkov
public import SHE.HeatKernelLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.CircleModulus
open MeasureTheory AddCircle CircleHeat HeatMarkov
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem memLp (f : CircleL2) : MemLp (fun x : AddCircle (1:ℝ) => (‖f x‖:ℂ)) 2 haarAddCircle :=
  (Lp.memLp f).of_le
    (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f).norm)
    (Filter.Eventually.of_forall (fun x => by simp))

def value (f : CircleL2) : CircleL2 := (memLp f).toLp (fun x => (‖f x‖:ℂ))

theorem value_ae (f : CircleL2) : value f =ᵐ[haarAddCircle] (fun x : AddCircle (1:ℝ) => (‖f x‖:ℂ)) :=
  (memLp f).coeFn_toLp

theorem norm_eq (f : CircleL2) : ‖value f‖=‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [value_ae f] with x hx
  rw [hx]
  simp

theorem normOne_eq (f : CircleL2) : normOne (value f)=normOne f := by
  apply integral_congr_ae
  filter_upwards [value_ae f] with x hx
  rw [hx]
  simp

/-- Positive heat convolution of the literal modulus represents the
absolute kernel majorant exactly, before any operator estimate. -/
theorem heat_norm_ae {t : ℝ} (ht : 0 < t) (f : CircleL2) :
    ∀ᵐ x ∂haarAddCircle,‖heat t (value f) x‖=
      ∫ y : AddCircle (1:ℝ),‖kernel t ht (y-x)‖*‖f y‖ ∂haarAddCircle := by
  filter_upwards [heat_convolution_ae ht (value f)] with x hx
  rw [hx]
  have he : (fun y : AddCircle (1:ℝ) => kernel t ht (y-x)*value f y) =ᵐ[haarAddCircle]
      (fun y => ((‖kernel t ht (y-x)‖*‖f y‖:ℝ):ℂ)) := by
    filter_upwards [value_ae f] with y hy
    rw [hy,Complex.ofReal_mul,kernel_norm_eq_re ht]
    congr 1
    exact Complex.ext (by simp) (by simpa using (kernel_real_nonneg ht (y-x)).1)
  rw [integral_congr_ae he]
  have ho := integral_complex_ofReal (μ := haarAddCircle)
    (f := fun y : AddCircle (1:ℝ) => ‖kernel t ht (y-x)‖*‖f y‖)
  rw [ho,Complex.norm_real,Real.norm_of_nonneg]
  exact integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

end SHE.CircleModulus
