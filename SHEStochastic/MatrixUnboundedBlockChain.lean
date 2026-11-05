module

public import SHEStochastic.MatrixUnboundedWeakExistence
public import SHEStochastic.MatrixGlobalBlockFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedBlockChain
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1) (H : ℝ≥0)

/-- The original unbounded equation and finite full-path energy are
retained for every selected block; they do not assume uniqueness. -/
structure Dynamics (Q : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H)) where
  energy : Integrable (fun x => ‖x.1‖^2) Q.toMeasure
  brownian : ∀ m (j : Fin m → Fin n×HaarNode),FiniteBrownianLawOn
    (CanonicalStateDriverFiltration.filtration H) Q.toMeasure H
    (fun i => CanonicalStateDriverFiltration.coordinate H (j i))
    (fun i k => if j i=j k then 1 else 0)
  equation : ∀ (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ),
    MatrixUnboundedFourierRecognition.Solves H Q.toMeasure G hG hβ hβ1.le energy brownian i a freq

abbrev Data := MatrixCanonicalBlockChain.Data H
  (fun Q => Nonempty (Dynamics G hG hβ hβ1 H Q))

theorem memLp_state (Q : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H))
    (hEnergy : Integrable (fun x => ‖x.1‖^2) Q.toMeasure) (t : ℝ≥0) :
    MemLp (MatrixLocalBlockChain.state H t) 2 Q.toMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (MatrixLocalBlockChain.state_measurable H t).stronglyMeasurable.aestronglyMeasurable).mpr
  apply hEnergy.mono'
    ((MatrixLocalBlockChain.state_measurable H t).norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (x.1.norm_coe_le_norm (CanonicalStateDriverFiltration.clock H t)) 2

variable (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ)

include hell hLower in
/-- Select only the countable succession of random-initial solution
laws needed for continuation. No pointwise measurable selection is used. -/
theorem exists_data (hH : (H : ℝ)≤1) (hH0 : 0<H) : Nonempty (Data G hG hβ hβ1 H) := by
  classical
  let S := fun ρ : MatrixLocalBlockChain.L2Law (n := n) => Classical.choice
    (MatrixUnboundedWeakExistence.exists_solution G hG hβ hβ1 ρ H ell hell hLower hH hH0)
  have hi (ρ : MatrixLocalBlockChain.L2Law (n := n)) :
      CanonicalInitialKernel.initialLaw H (S ρ).law.toMeasure=ρ.val.toMeasure := by
    change (S ρ).law.toMeasure.map (CanonicalStateDriverFiltration.state H 0)=_
    have h0 : CanonicalStateDriverFiltration.state (E := Physical (d := Fin n))
        (ι := Fin n×HaarNode) H 0=(fun x => x.1 (StoppedPathPasting.origin H)) := by
      funext x
      simp [CanonicalStateDriverFiltration.state,CanonicalStateDriverFiltration.clock,StoppedPathPasting.origin]
    rw [h0]
    exact (S ρ).initial
  refine ⟨⟨fun ρ => ⟨(S ρ).law,hi ρ,⟨⟨(S ρ).energy,(S ρ).brownian,(S ρ).equation⟩⟩,
    fun t _ => memLp_state H (S ρ).law (S ρ).energy t⟩,fun ρ => ?_⟩⟩
  filter_upwards [CanonicalInitialBrownianKernel.law H (S ρ).law.toMeasure (S ρ).brownian] with z hz
  exact ⟨hz,trivial⟩

end SHEStochastic.MatrixUnboundedBlockChain
