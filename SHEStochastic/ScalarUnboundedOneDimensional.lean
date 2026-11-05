module

public import SHEStochastic.MatrixUnboundedMildWeakExistence
public import SHEStochastic.MatrixAnalyticNegativeKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnboundedOneDimensional
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator MatrixOrder

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (Physical (d := Fin 1)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin 1)) := borel _
local instance : BorelSpace (Physical (d := Fin 1)) := ⟨rfl⟩

/-- The original scalar amplitude as a single-component matrix. -/
def coefficient (g : ℝ→ℝ) (z : EuclideanSpace ℝ (Fin 1)) : Matrix (Fin 1) (Fin 1) ℝ :=
  g (z 0) • 1

theorem scalar_distance (z w : EuclideanSpace ℝ (Fin 1)) : dist (z 0) (w 0)=dist z w := by
  rw [EuclideanSpace.dist_eq,Fin.sum_univ_one,Real.sqrt_sq dist_nonneg]

theorem coefficient_distance (g : ℝ→ℝ) (z w : EuclideanSpace ℝ (Fin 1)) :
    dist (coefficient g z) (coefficient g w)=dist (g (z 0)) (g (w 0)) := by
  rw [dist_eq_norm,dist_eq_norm]
  simp only [coefficient,←sub_smul,norm_smul,norm_one,mul_one]

theorem holder {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) : HolderWith C β (coefficient g) := by
  intro z w
  have h := hg (z 0) (w 0)
  simpa only [edist_dist,←coefficient_distance g z w,scalar_distance z w] using h

theorem elliptic {g : ℝ→ℝ} (ell : ℝ) (he : ∀ z,ell≤(g z)^2)
    (z : EuclideanSpace ℝ (Fin 1)) :
    ell • (1 : Matrix (Fin 1) (Fin 1) ℝ)≤coefficient g z*(coefficient g z).conjTranspose := by
  have h : coefficient g z*(coefficient g z).conjTranspose=(g (z 0))^2 • 1 := by
    simp [coefficient,pow_two,smul_smul]
  rw [h]
  exact smul_le_smul_of_nonneg_right (he _) Matrix.PosSemidef.one.nonneg

/-- Embed the actual scalar L² initial state as the unique vector
component, with the original unit-torus spatial measure. -/
def initial (u : RealL2) : Physical (d := Fin 1) :=
  VectorHeat.coordinates.symm (WithLp.toLp 2 (fun _ : Fin 1 => u))

theorem initial_component (u : RealL2) : VectorHeatObservation.component (0 : Fin 1) (initial u)=u := by
  change VectorHeat.coordinates (initial u) 0 = _
  rw [initial,LinearIsometryEquiv.apply_symm_apply]

theorem component_heat (t : ℝ) (u : Physical (d := Fin 1)) :
    VectorHeatObservation.component (0 : Fin 1) (VectorAnalyticHeat.heat t u)=
      NativeHeatObservation.heat t (VectorHeatObservation.component (0 : Fin 1) u) :=
  MatrixAnalyticNegativeKernel.component_heat _ _ _

/-- The existing global unbounded weak-existence construction applies
with exactly the original scalar coefficient in dimension one. -/
theorem exists_vector_realization {g : ℝ→ℝ} {C β : ℝ≥0}
    (hg : HolderWith C β g) (hβ : 0<β) (hβ1 : β<1)
    (u : RealL2) (ell : ℝ) (hell : 0<ell) (he : ∀ z,ell≤(g z)^2) :
    Nonempty (MatrixUnboundedGlobalFourierAll.FullSolution (coefficient g) (holder hg) hβ hβ1
      (MatrixUnboundedGlobalFourierAll.pointLaw (initial u))) :=
  MatrixUnboundedGlobalFourierAll.exists_deterministic_full_solution (coefficient g) (holder hg)
    hβ hβ1 (initial u) ell hell (elliptic ell he)

end SHEStochastic.ScalarUnboundedOneDimensional
