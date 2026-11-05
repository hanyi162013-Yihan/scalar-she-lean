module

public import SHEStochastic.MatrixInfiniteHaar
public import SHEStochastic.MatrixFrobeniusNorm
public import SHE.LpIntegralFubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixProfileHilbert
open MeasureTheory Matrix SHE SHE.FiniteTransport MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable (d : Type*) [Fintype d] [DecidableEq d]

abbrev Fiber := EuclideanSpace ℝ (d × d)

/-- Matrix profiles use the genuine Frobenius Hilbert geometry. Matrix
operator norms are retained in the finite-dimensional coefficient maps. -/
def coordinates : Fiber d ≃ₗ[ℝ] Matrix d d ℝ where
  toFun v i j := v (i,j)
  invFun A := WithLp.toLp 2 (fun p => A p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def toMatrix : Fiber d →L[ℝ] Matrix d d ℝ := (coordinates d).toContinuousLinearEquiv.toContinuousLinearMap
def toVector : Matrix d d ℝ →L[ℝ] Fiber d := (coordinates d).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem norm_vector (A : Matrix d d ℝ) : ‖toVector d A‖=MatrixFrobeniusNorm.size A := by
  apply (sq_eq_sq₀ (norm_nonneg _) (MatrixFrobeniusNorm.nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, MatrixFrobeniusNorm.square]
  simp only [toVector, coordinates, frobeniusSq, Fintype.sum_prod_type]
  rfl

local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
abbrev Space := Lp (Fiber d) 2 μ

def mass (s : Set (AddCircle (1 : ℝ))) : Space d →L[ℝ] Matrix d d ℝ :=
  (toMatrix d).comp (LpIntegralFubini.setIntegralCLM μ s)

theorem memLp (P : Profile d) : MemLp (fun x => toVector d (P.value x)) 2 μ :=
  MemLp.of_bound ((toVector d).continuous.comp_aestronglyMeasurable P.measurable.aestronglyMeasurable)
    (‖toVector d‖*(P.bound : ℝ)) (P.norm_bound.mono (fun x hx =>
      ((toVector d).le_opNorm (P.value x)).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))))

def realize (P : Profile d) : Space d := (memLp d P).toLp _

theorem realize_ae (P : Profile d) :
    ⇑(realize d P) =ᵐ[μ] fun x => toVector d (P.value x) := (memLp d P).coeFn_toLp

/-- Integration in the Frobenius profile Hilbert space gives precisely
the literal matrix interval masses already used by the global factor. -/
theorem mass_realize (P : Profile d) (s : Set (AddCircle (1 : ℝ))) :
    mass d s (realize d P)=MatrixHaarFunctions.mass μ P.value s := by
  have hi : Integrable (realize d P) ((μ).restrict s) :=
    ((Lp.memLp (realize d P)).integrable (by norm_num : (1 : ENNReal)≤2)).integrableOn
  change toMatrix d (∫ x in s, realize d P x ∂μ)=_
  rw [← (toMatrix d).integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (realize_ae d P)] with x hx
  rw [hx]
  exact (coordinates d).apply_symm_apply (P.value x)

end SHEStochastic.MatrixProfileHilbert
