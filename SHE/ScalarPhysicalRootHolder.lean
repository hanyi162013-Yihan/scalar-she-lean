module
public import SHE.PhysicalLeafHolder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates PhysicalScoreChain
local instance scalarPhysicalRootHolder_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {N:ℕ} (L:Level R X 1)

/-- A genuine scalar root Hölder modulus gives its exact selected
directional modulus inside every physical all-order word. -/
theorem initial_directional_holder {H β:ℝ}
    (hh:∀p z w,|L.test p z-L.test p w|≤H*|z 0-w 0|^β)
    (k:ℕ)(p:History X k)(g:Fin (1+k)→Fin N)(d x:WordRecursion.State N)(s t:ℝ):
    |initial L k p g (x+s • d)-initial L k p g (x+t • d)|≤
      (H*|d (rootSelector k g 0)|^β)*|s-t|^β:=by
  let i:=rootSelector k g 0
  have h:=hh (rootParameter k p) (projection (rootSelector k g) (x+s • d))
    (projection (rootSelector k g) (x+t • d))
  simp only [projection_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at h
  rw [show x i+s*d i-(x i+t*d i)=(s-t)*d i by ring,abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _)] at h
  exact h.trans_eq (by dsimp only [i] <;> ring)

end SHE.PhysicalChainArrays
