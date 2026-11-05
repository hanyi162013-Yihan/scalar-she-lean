module

public import SHEStochastic.MatrixHaarJetBounds
public import SHEStochastic.DirectionalJetFrechet

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixHaarFrechetBounds
open Matrix MatrixFrobeniusNorm MatrixHaarJetBounds Filter
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff Topology

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The child estimates in ordinary iterated Fréchet-derivative
notation, with every perturbation direction explicit. -/
theorem children (a b : Matrix d d ℝ) (L R : E →L[ℝ] Matrix d d ℝ)
    (s : Set E) (hs : IsOpen s)
    (hp : ∀ y∈s, (a+L y).PosDef ∧ (b+R y).PosDef)
    (x : E) (hx : x∈s) (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hLo : m • (1 : Matrix d d ℝ) ≤ a+L x ∧ m • (1 : Matrix d d ℝ) ≤ b+R x)
    (hHi : a+L x ≤ U • (1 : Matrix d d ℝ) ∧ b+R x ≤ U • (1 : Matrix d d ℝ))
    (n : ℕ) (hn : 0 < n) (v : Fin n → E) :
    size (iteratedFDeriv ℝ n (fun y => MatrixHaarAlgebra.left (a+L y) (b+R y)) x v) ≤
        childConstant d m U n*(∏ i : Fin n, (size (L (v i))+size (R (v i)))) ∧
    size (iteratedFDeriv ℝ n (fun y => MatrixHaarAlgebra.right (a+L y) (b+R y)) x v) ≤
        childConstant d m U n*(∏ i : Fin n, (size (L (v i))+size (R (v i)))) := by
  have hSmooth := MatrixHaarSmooth.children (k := ∞)
    (contDiffAt_const.add L.contDiff.contDiffAt) (contDiffAt_const.add R.contDiff.contDiffAt)
    (hp x hx).1 (hp x hx).2
    ((show ∀ᶠ y in 𝓝 x, y∈s from hs.mem_nhds hx).mono fun y hy => hp y hy)
  have hw : (List.ofFn v).reverse≠[] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_reverse, List.length_ofFn, List.length_nil] at hh
    omega
  rw [← DirectionalJets.eq_iterated hSmooth.1 n v,
    ← DirectionalJets.eq_iterated hSmooth.2 n v]
  have hh := MatrixHaarJetBounds.children a b L R s hs hp x hx m U hm hU hLo hHi
    (List.ofFn v).reverse hw
  simpa [MatrixJetClosure.weight, List.map_reverse, List.prod_reverse, List.map_ofFn,
    List.prod_ofFn] using hh

end SHEStochastic.MatrixHaarFrechetBounds
