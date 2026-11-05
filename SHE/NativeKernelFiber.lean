module

public import SHE.NativeKernelReindex
public import SHE.RawNoiseSupport

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.NativeRandomKernel
open StoppedFourier
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Vanishing of one actual spatial fiber suffices; no other random
reference profile is frozen or changed. -/
theorem integralOperator_eq_zero_of_fiber (F : Ω×(HeatCircle×HeatCircle)→ℂ) (ω : Ω)
    (h : ∀ y x,F (ω,(y,x))=0) : integralOperator F ω=0 := by
  have hh:=integralOperator_reindex F (fun _ : Unit=>ω) ()
  have he : (fun z : Unit×(HeatCircle×HeatCircle)=>F (ω,z.2))=0 := by
    funext z
    exact h z.2.1 z.2.2
  rw [he,integralOperator_zero] at hh
  exact hh.symm

end SHE.NativeRandomKernel
