module

public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.FiniteKernelProduct
open Set MeasureTheory ProbabilityTheory
variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]

/-- A finite product kernel on the actual original coordinate tuple. -/
def kernel : (r : ℕ) → (Fin r → Kernel X E) → Kernel X (Fin r → E)
  | 0,_ => Kernel.deterministic (fun _ => Fin.elim0) measurable_const
  | r+1,κ => Kernel.map ((κ 0).prod (kernel r (fun j => κ j.succ)))
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => E) 0).symm

instance kernel_markov (r : ℕ) (κ : Fin r → Kernel X E) [∀ j,IsMarkovKernel (κ j)] :
    IsMarkovKernel (kernel r κ) := by
  induction r with
  | zero => unfold kernel; infer_instance
  | succ r ih =>
    letI : IsMarkovKernel (kernel r (fun j => κ j.succ)) := ih (fun j => κ j.succ)
    exact Kernel.IsMarkovKernel.map _
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => E) 0).symm.measurable

theorem kernel_apply (r : ℕ) (κ : Fin r → Kernel X E) [∀ j,IsMarkovKernel (κ j)] (x : X) :
    kernel r κ x = Measure.pi (fun j => κ j x) := by
  induction r with
  | zero =>
    change Measure.dirac (Fin.elim0 : Fin 0 → E) = _
    rw [Measure.pi_of_empty]
    congr 1
  | succ r ih =>
    rw [kernel,Kernel.map_apply _
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => E) 0).symm.measurable,
      Kernel.prod_apply,ih]
    simpa only [Fin.succAbove_zero] using
      (measurePreserving_piFinSuccAbove (fun j => κ j x) 0).symm.map_eq

/-- Jointly Borel integrands remain Borel after averaging the original
finite family of parameter-dependent probability kernels. -/
theorem measurable_integral (r : ℕ) (κ : Fin r → Kernel X E) [∀ j,IsMarkovKernel (κ j)]
    (F : X × (Fin r → E) → ℝ) (hF : Measurable F) :
    Measurable (fun x => ∫ y,F (x,y) ∂Measure.pi (fun j => κ j x)) := by
  have h := (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := kernel r κ)).measurable
  simpa only [kernel_apply] using h

end SHE.FiniteKernelProduct
