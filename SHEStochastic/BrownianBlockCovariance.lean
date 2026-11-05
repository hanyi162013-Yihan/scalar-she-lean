module

public import SHEStochastic.NNRealBlockClock
public import SHE.BrownianFiniteCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BrownianBlockCovariance
open SHE
open scoped NNReal
variable {ι : Type*} [DecidableEq ι] {m : ℕ}

/-- The finite covariance sum of the actual elapsed block pieces is
exactly the Brownian covariance, including repeated coordinate labels
and arbitrary simultaneous observation times. -/
theorem sum (H : ℝ≥0) (a : Fin m → ι) (t : Fin m → ℝ≥0) (M : ℕ)
    (ht : ∀ i,t i≤(M+1 : ℕ)*H) :
    (∑ k : Fin (M+1),BrownianFiniteCovariance.matrix a (fun i => NNRealBlockClock.clock H k (t i)))=
      BrownianFiniteCovariance.matrix a t := by
  ext i l
  simp only [Matrix.sum_apply,BrownianFiniteCovariance.matrix,←Finset.sum_mul]
  congr 1
  have hh : (∑ k : Fin (M+1),min (NNRealBlockClock.clock H k (t i))
      (NNRealBlockClock.clock H k (t l)))=min (t i) (t l) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => min (NNRealBlockClock.clock H k (t i))
      (NNRealBlockClock.clock H k (t l))) (M+1)]
    exact NNRealBlockClock.sum_min H (t i) (t l) M (ht i) (ht l)
  exact_mod_cast hh

end SHEStochastic.BrownianBlockCovariance
