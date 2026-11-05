module
public import SHE.ProfileL2
public import Mathlib.Algebra.Order.Chebyshev
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.ScalarFiniteEnergy
open MeasureTheory ProfileL2
open scoped BigOperators
variable {X ι:Type*}[MeasurableSpace X][Fintype ι]

/-- A true finite sum of L2 fields has its square energy bounded by the
number of terms times the sum of their energies. -/
theorem sum_bound (μ:Measure X)(F:ι→X→ℝ)(hF:∀j,MemLp (F j) 2 μ):
    Integrable (fun x=>(∑j,F j x)^2) μ ∧
      (∫x,(∑j,F j x)^2 ∂μ)≤(Fintype.card ι:ℝ)*∑j,∫x,(F j x)^2 ∂μ:=by
  classical
  have hsum:MemLp (fun x=>∑j,F j x) 2 μ:=memLp_finsetSum Finset.univ (fun j _=>hF j)
  have hi:Integrable (fun x=>∑j,(F j x)^2) μ:=
    integrable_finset_sum Finset.univ (fun j _=>(hF j).integrable_sq)
  refine ⟨hsum.integrable_sq,?_⟩
  have hh:=integral_mono hsum.integrable_sq (hi.const_mul (Fintype.card ι:ℝ))
    (fun x=>by simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => F j x)))
  rw [integral_const_mul,integral_finset_sum Finset.univ (fun j _=>(hF j).integrable_sq)] at hh
  exact hh
end SHE.ScalarFiniteEnergy
