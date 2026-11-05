module
public import SHE.ScalarFiniteEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.ScalarFiniteEnergyAdd
open MeasureTheory ProfileL2
open scoped BigOperators
variable {X ι:Type*}[MeasurableSpace X][Fintype ι]

/-- Covariance plus the finite full-age baseline contributions have
ordinary finite-sum output energy. -/
theorem bound (μ:Measure X)(f:X→ℝ)(g:ι→X→ℝ)
    (hf:MemLp f 2 μ)(hg:∀j,MemLp (g j) 2 μ):
    Integrable (fun x=>(f x+∑j,g j x)^2) μ ∧
      (∫x,(f x+∑j,g j x)^2 ∂μ)≤((Fintype.card ι:ℝ)+1)*
        ((∫x,(f x)^2 ∂μ)+∑j,∫x,(g j x)^2 ∂μ):=by
  classical
  let F:Option ι→X→ℝ:=fun j=>j.elim f g
  have hF:∀j,MemLp (F j) 2 μ:=by
    intro j
    cases j with
    | none=>exact hf
    | some j=>exact hg j
  have hh:=ScalarFiniteEnergy.sum_bound μ F hF
  simpa only [F,Fintype.sum_option,Fintype.card_option,Nat.cast_add,Nat.cast_one,
    Option.elim_none,Option.elim_some] using hh
end SHE.ScalarFiniteEnergyAdd
