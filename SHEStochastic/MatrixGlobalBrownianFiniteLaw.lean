module

public import SHEStochastic.MatrixFreshBlockBrownian
public import SHEStochastic.KernelMarkovGaussianSum
public import SHEStochastic.CountablePathFiniteSum
public import SHEStochastic.BrownianBlockCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixGlobalBrownianFiniteLaw
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

def observations (H : ℝ≥0) {m : ℕ} (a : Fin m → Fin n×HaarNode) (t : Fin m → ℝ≥0)
    (p : MatrixGlobalBlockPath.Space (n := n) H) : WordRecursion.State m :=
  WithLp.toLp 2 (fun i => MatrixGlobalBlockPath.driver H (a i) (t i) p)

/-- The actual pasted driver has every finite Brownian Gaussian law
at arbitrary finite times. All local noises are those of the original
solution chain; no independent-copy replacement is made. -/
theorem law (hH0 : 0<H) (m : ℕ) (a : Fin m → Fin n×HaarNode) (t : Fin m → ℝ≥0)
    (M : ℕ) (ht : ∀ i,t i≤(M+1 : ℕ)*H) :
    HasLaw (observations H a t)
      (multivariateGaussian (0 : WordRecursion.State m) (BrownianFiniteCovariance.matrix a t)) (D.law ρ₀) := by
  let times := fun j i => NNRealBlockClock.clock H j (t i)
  let f := fun j => MatrixFreshBlockBrownian.observations (H := H) a (times j)
  let A := fun j => BrownianFiniteCovariance.matrix a (times j)
  have htime (j i) : times j i≤H := NNRealBlockClock.clock_le H j (t i)
  have h0 : HasLaw (fun p : MatrixGlobalBlockPath.Space (n := n) H => f 0 (p 0))
      (multivariateGaussian (0 : WordRecursion.State m) (A 0)) (D.law ρ₀) :=
    (MatrixFreshBlockBrownian.block_law D ρ₀ 0 m a (times 0) (htime 0)).comp
      ⟨(measurable_pi_apply 0).aemeasurable,D.marginals ρ₀ 0⟩
  have hh := KernelMarkovGaussianSum.law (D.law ρ₀) f
    (fun j => MatrixFreshBlockBrownian.observations_measurable a (times j)) A
    (fun j => BrownianFiniteCovariance.posSemidef a (times j)) h0
    (fun j => MatrixFreshBlockBrownian.prefix_law D ρ₀ j m a (times (j+1)) (htime (j+1))) M
  have hcov : (∑ k : Fin (M+1),A k)=BrownianFiniteCovariance.matrix a t :=
    BrownianBlockCovariance.sum H a t M ht
  rw [hcov] at hh
  apply hh.congr
  filter_upwards [MatrixBlockContinuation.all_zero D ρ₀] with p hp
  apply PiLp.ext
  intro i
  change MatrixGlobalBlockPath.driver H (a i) (t i) p=_
  rw [MatrixGlobalBlockPath.driver,CountablePathFiniteSum.value_sum_of_zero H hH0
    (fun j s => CanonicalStateDriverFiltration.coordinate H (a i) s (p j)) (fun j => hp j (a i)) M (t i) (ht i)]
  simp only [KernelMarkovGaussianSum.sum,f,MatrixFreshBlockBrownian.observations,
    WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,times]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- A convenient covering version with no externally chosen cutoff. -/
theorem law_of_cover (hH0 : 0<H) (m : ℕ) (a : Fin m → Fin n×HaarNode) (t : Fin m → ℝ≥0) :
    HasLaw (observations H a t)
      (multivariateGaussian (0 : WordRecursion.State m) (BrownianFiniteCovariance.matrix a t)) (D.law ρ₀) := by
  let M := Finset.univ.sup (fun i => ⌈t i/H⌉₊)
  apply law D ρ₀ hH0 m a t M
  intro i
  exact (CountablePathConcatenation.covering H (t i) hH0).trans (by
    gcongr
    exact Finset.le_sup (f := fun i => ⌈t i/H⌉₊) (Finset.mem_univ i))

end SHEStochastic.MatrixGlobalBrownianFiniteLaw
