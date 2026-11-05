module

public import SHEStochastic.MatrixJetSegment
public import SHEStochastic.MatrixHaarKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixFactorHeatStability
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixPhysicalColumnSmooth
  MatrixColumnComparison MatrixProfileInterpolation
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (P Q : Profile d) : ℝ := MatrixHaarHigherFamily.constant (blend P Q 0 ⟨le_rfl,zero_le_one⟩) 0

theorem constant_nonneg (P Q : Profile d) : 0 ≤ constant P Q := MatrixHaarHigherFamily.constant_nonneg _ _

/-- Full Hilbert--Schmidt one-input stability for the actual infinite
Haar heat factor, obtained by the already proved common segment argument. -/
theorem bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (P Q : Profile d) :
    ‖MatrixHaarKernel.kernel t Q-MatrixHaarKernel.kernel t P‖^2 ≤
      constant P Q*t^(-(1/2 : ℝ))*‖difference P Q‖^2 := by
  have hc : 0 ≤ constant P Q*t^(-(1/2 : ℝ))*‖difference P Q‖^2 :=
    mul_nonneg (mul_nonneg (constant_nonneg P Q) (Real.rpow_nonneg ht.le _)) (sq_nonneg _)
  have he := MatrixJetSegment.energy P Q [] (VectorHeat.heat t)
    (constant P Q*t^(-(1/2 : ℝ))*‖difference P Q‖^2) hc (by
      intro s hs
      have hh := MatrixHaarHigherFamily.energy ht ht1 (blend P Q s hs) (difference P Q) []
        (fun _ => 0) (fun _ => le_rfl) (by simp)
      have heq : MatrixHaarHigherFamily.constant (blend P Q s hs) 0=constant P Q := rfl
      simpa only [List.length_nil,MatrixJetClosure.weight,List.map_nil,List.prod_nil,one_pow,mul_one,heq] using hh)
  have hcol (k : d × HaarNode) :
      VectorHeat.heat t (MatrixHaarHigherFamily.jet Q [] k-MatrixHaarHigherFamily.jet P [] k)=
        (MatrixHaarKernel.kernel t Q-MatrixHaarKernel.kernel t P) k := by
    simp only [MatrixHaarHigherFamily.jet,DirectionalJets.jet,map_sub,
      MatrixHaarHigherFamily.column_realize,lp.coeFn_sub,Pi.sub_apply,MatrixHaarKernel.column,if_pos ht]
  rw [HilbertColumns.norm_sq]
  simpa only [hcol] using he.2

end SHEStochastic.MatrixFactorHeatStability
