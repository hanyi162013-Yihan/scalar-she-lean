module

public import SHEStochastic.MatrixUnboundedFourierRecognition
public import SHEStochastic.MatrixUnboundedLimitSquare

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedWeakExistence
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal Topology MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (H : ℝ≥0)

/-- A continuous canonical vector weak solution of the literal unbounded
matrix Fourier equations, with its original Brownian driver and initial law.
No global bound on the coefficient is a field of this structure. -/
structure Solution where
  law : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
    (ι := Fin n×FiniteHaar.HaarNode) H)
  energy : Integrable (fun x => ‖x.1‖^2) law.toMeasure
  brownian : ∀ m (j : Fin m → Fin n×FiniteHaar.HaarNode),FiniteBrownianLawOn
    (CanonicalStateDriverFiltration.filtration H) law.toMeasure H
    (fun i => CanonicalStateDriverFiltration.coordinate H (j i))
    (fun i k => if j i=j k then 1 else 0)
  initial : law.toMeasure.map (fun x => x.1 (StoppedPathPasting.origin H))=ρ₀.val.toMeasure
  equation : ∀ (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ),
    MatrixUnboundedFourierRecognition.Solves H law.toMeasure G hG hβ hβ1.le energy brownian i a freq

variable (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ)

include hell hLower in
/-- Local weak existence for every square-integrable random initial law:
the probability space, Brownian driver, and unbounded equation are all
constructed from actual bounded-cutoff solutions. -/
theorem exists_solution (hH : (H : ℝ)≤1) (hH0 : 0<H) :
    Nonempty (Solution G hG hβ hβ1 ρ₀ H) := by
  obtain ⟨S,R,Q,φ,hφ,hlim,hBrown,hInitial⟩ :=
    MatrixUnboundedLawCompactness.exists_cutoff_joint_limit G hG hβ hβ1 ell hell hLower
      ρ₀ (fun m => (m : ℝ≥0)) H hH hH0
  have hEnergy := MatrixUnboundedLawEnergy.limit_energy G hG hβ hβ1 ell hell hLower
    ρ₀ (fun m => (m : ℝ≥0)) S R H hH hH0 Q φ hlim
  refine ⟨⟨Q,hEnergy,hBrown,hInitial,fun i a freq => ?_⟩⟩
  exact MatrixUnboundedFourierRecognition.equation H Q.toMeasure G hG hβ hβ1.le hEnergy hBrown i a freq
    (MatrixUnboundedLimitSquare.linear G hG hβ hβ1 ell hell hLower ρ₀ S R H hH hH0 Q φ hlim i a freq)
    (fun t _ => MatrixUnboundedLimitSquare.memLp G hG hβ hβ1 ell hell hLower
      ρ₀ S R H hH hH0 Q φ hlim i a freq t)
    (MatrixUnboundedLimitSquare.square G hG hβ hβ1 ell hell hLower ρ₀ S R H hH hH0 Q φ hφ hlim i a freq)
    (fun k => MatrixUnboundedLimitSquare.mixed G hG hβ hβ1 ell hell hLower
      ρ₀ S R H hH hH0 Q φ hφ hlim i a freq k)

end SHEStochastic.MatrixUnboundedWeakExistence
