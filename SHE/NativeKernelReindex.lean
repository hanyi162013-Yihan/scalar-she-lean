module

public import SHE.NativeRandomKernel

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.NativeRandomKernel
open StoppedFourier
variable {P W : Type*} [MeasurableSpace P] [MeasurableSpace W]

/-- The canonical integral operator depends only on its spatial fiber,
so changing its outer parameterization changes no physical operator. -/
theorem integralOperator_reindex (F : P×(HeatCircle×HeatCircle)→ℂ) (f : W→P) (w : W) :
    integralOperator (fun z : W×(HeatCircle×HeatCircle)=>F (f z.1,z.2)) w=integralOperator F (f w) := by
  rfl

end SHE.NativeRandomKernel
