module
public import SHE.FiniteCenteredProduct
public import SHE.SmoothCylinderAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.FiniteCenteredSmooth
open SmoothCylinders FiniteCenteredProduct
variable {E:Type} {ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]

theorem product (s:Finset ι)(a:ι→E→ℝ)(b:ι→ℝ)
    (ha:∀i∈s,BoundedSmooth (a i)):
    BoundedSmooth (fun z=>∏i∈s,(a i z-b i)):=by
  induction s using Finset.induction_on with
  | empty=>simpa only [Finset.prod_empty] using (BoundedSmooth.const (E:=E) (1:ℝ))
  | @insert i s hi ih=>
    have hs:∀j∈s,BoundedSmooth (a j):=fun j hj=>ha j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.prod_insert hi] using
      ((ha i (Finset.mem_insert_self i s)).sub (BoundedSmooth.const (b i))).mul (ih hs)

/-- The complete centered word remains bounded smooth for arbitrary
frozen baseline values; no baseline derivative is discarded. -/
theorem test (s:Finset ι)(R:E→ℝ)(a:ι→E→ℝ)(b:ι→ℝ)
    (hR:BoundedSmooth R)(ha:∀i∈s,BoundedSmooth (a i)):
    BoundedSmooth (FiniteCenteredProduct.test s R a b):=
  hR.mul (product s a b ha)
end SHE.FiniteCenteredSmooth
