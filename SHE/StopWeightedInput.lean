module

public import SHE.StopWeightedRows
public import SHE.PhysicalMeanRange
public import SHE.WeightedMeanFactorization

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.StopWeightedInput
open Set MeasureTheory AddCircle Real StoppedFourier WordRecursion StopWeightedRows
  FiniteHeatRows PhysicalMeanRange StoppedGaussianScore
open scoped BigOperators
local instance stopWeightedInput_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- A true signed L2 input acts through the stop-weighted physical row.
The finite derivative functional, its q-law, and each original stopping
weight are unchanged. No Gaussian assumption is imposed on the input. -/
theorem functional_dampedDirection (D : WordRecursion.State n→L[ℝ]ℝ)
    (Λ q : ℝ) (Z : Fin n→Observation) (hr : ∀ i,q<(Z i).target) (v : CircleL2) :
    D (dampedDirection (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ v)=
      (FiniteHeatRows.functional (D.comp (diagonal (weights Λ Z q))) Z q v).re := by
  rw [FiniteHeatRows.apply_eq_sum]
  change (∑ i : Fin n,coefficient D i*(exp (-Λ*((Z i).stop-q))*
    PhysicalProfile.physicalHeatMean v ((Z i).target-q,
      nativeCenter (fun i=>NativeHeatSpan.unitCenter (Z i).center) i)))=_
  change _=(inner ℂ (StopWeightedRows.kernel D Λ Z q q) v).re
  rw [StopWeightedRows.kernel_eq_sum,sum_inner,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left,Complex.conj_ofReal,PhysicalProfile.physicalHeatMean_eq (sub_pos.mpr (hr i))]
  have hc : nativeCenter (fun i=>NativeHeatSpan.unitCenter (Z i).center) i=(Z i).center :=
    NativeHeatSpan.scale_inverse _
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,weights]
  ring

theorem weighted_product_integrable (D : WordRecursion.State n→L[ℝ]ℝ)
    (Λ q : ℝ) (Z : Fin n→Observation) (hr : ∀ i,q<(Z i).target) (v : CircleL2) :
    Integrable (fun y : HeatCircle => ((D (weightedHeatRow Λ Z q q y):ℝ):ℂ)*v y) haarAddCircle := by
  apply (L2.integrable_inner (StopWeightedRows.kernel D Λ Z q q) v).congr
  filter_upwards [StopWeightedRows.kernel_ae D Λ Z q q hr] with y hy
  rw [hy,RCLike.inner_apply,Complex.conj_ofReal]
  exact mul_comm _ _

theorem dampedDirection_integral (D : WordRecursion.State n→L[ℝ]ℝ)
    (Λ q : ℝ) (Z : Fin n→Observation) (hr : ∀ i,q<(Z i).target) (v : CircleL2) :
    D (dampedDirection (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ v)=
      ∫ y : HeatCircle,D (weightedHeatRow Λ Z q q y)*(v y).re ∂haarAddCircle := by
  rw [functional_dampedDirection D Λ q Z hr v,
    FiniteHeatRows.functional_integral (D.comp (diagonal (weights Λ Z q))) Z hr v]
  change RCLike.re (∫ y : HeatCircle,((D (weightedHeatRow Λ Z q q y):ℝ):ℂ)*v y ∂haarAddCircle)=_
  rw [←integral_re (weighted_product_integrable D Λ q Z hr v)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change (((D (weightedHeatRow Λ Z q q y):ℝ):ℂ)*v y).re=_
    simp only [ContinuousLinearMap.comp_apply,weightedHeatRow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero])

end SHE.StopWeightedInput
