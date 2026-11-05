module

public import SHEStochastic.MatrixUnboundedFourierInput
public import SHEStochastic.MatrixUnboundedStateCovariance
public import SHEStochastic.NativeCrossCompensator
public import SHEStochastic.PathIntegratedCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixUnboundedNativeCompensator
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (G : EuclideanSpace ℝ d → Matrix d d ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (hEnergy : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H))
    (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
def diagonal : C(Physical (d := d),ℝ) :=
  ⟨StateNoiseCovariance.value (AddCircle.haarAddCircle (T := (1 : ℝ))) hβ hβ1
    (MatrixDiffusionRows.holder hG i) (MatrixDiffusionRows.holder hG i) (weight a n) (weight a n),
    StateNoiseCovariance.continuous _ hβ hβ1 _ _ _ _⟩

def mixed (b : Input (d := d)) : C(Physical (d := d),ℝ) :=
  ⟨StateDriverCovariance.value (AddCircle.haarAddCircle (T := (1 : ℝ))) hβ hβ1
    (MatrixDiffusionRows.holder hG i) (weight a n) (VectorWhiteCoordinates.analysis.symm b),
    StateDriverCovariance.continuous _ hβ hβ1 _ _ _⟩

theorem diagonal_apply (u : Physical (d := d)) :
    diagonal G hG hβ hβ1 i a n u=‖StateNoiseCovariance.row (AddCircle.haarAddCircle (T := (1 : ℝ))) hβ hβ1
    (MatrixDiffusionRows.holder hG i) (weight a n) u‖^2 :=
by
  change inner ℝ (StateNoiseCovariance.row _ hβ hβ1 (MatrixDiffusionRows.holder hG i) (weight a n) u)
    (StateNoiseCovariance.row _ hβ hβ1 (MatrixDiffusionRows.holder hG i) (weight a n) u)=_
  exact real_inner_self_eq_norm_sq _

theorem mixed_apply (b : Input (d := d)) (u : Physical (d := d)) :
    inner ℝ (VectorWhiteCoordinates.analysis (StateNoiseCovariance.row (AddCircle.haarAddCircle (T := (1 : ℝ))) hβ hβ1
    (MatrixDiffusionRows.holder hG i) (weight a n) u)) b=
      mixed G hG hβ hβ1 i a n b u := by
  conv_lhs => rhs;rw [← VectorWhiteCoordinates.analysis.apply_symm_apply b]
  exact VectorWhiteCoordinates.analysis.inner_map_map _ _

/-- The native quadratic compensator is the same continuous
state functional used in weak convergence, integrated along the path. -/
theorem energy_ae : ∀ᵐ ω ∂μ,∀ T : ℝ≥0,T ≤ H →
    PredictableBracket.energy (MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEnergy i a n) T ω=
      ∫ s in (0 : ℝ)..(T : ℝ),Real.exp (s*(2*(n : ℝ)^2))*
        diagonal G hG hβ hβ1 i a n (U (s.toNNReal,ω)) := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := PredictableL2.timeMeasure H)).quasiMeasurePreserving.ae
    (MatrixUnboundedFourierInput.input_ae F μ H G hG hβ hβ1 U hU hEnergy i a n)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hrow T hT
  change (∫ s,(Set.Iio T).indicator
    (fun s => ‖MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEnergy i a n (s,ω)‖^2) s ∂PredictableL2.timeMeasure H)=_
  rw [timeMeasure_eq] at hrow ⊢
  calc
    _ = ∫ s,(Set.Iio T).indicator (fun s : ℝ≥0 =>
        Real.exp ((s : ℝ)*(2*(n : ℝ)^2))*diagonal G hG hβ hβ1 i a n (U (s,ω))) s
          ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
      apply integral_congr_ae
      filter_upwards [hrow] with s hs
      by_cases ht : s < T
      · simp only [Set.indicator_apply,Set.mem_Iio,ht,ite_true]
        dsimp only [Prod.swap] at hs
        rw [hs,MatrixUnboundedFourierInput.row,norm_smul,Real.norm_eq_abs,LinearIsometryEquiv.norm_map]
        dsimp [FourierHeatInput.multiplier]
        rw [abs_of_pos (Real.exp_pos _),min_eq_left (show (s : ℝ) ≤ H from ht.le.trans hT),
          mul_pow,diagonal_apply,pow_two (Real.exp _),← Real.exp_add]
        congr 1
        congr 1
        ring
      · simp only [Set.indicator_apply,Set.mem_Iio,ht,ite_false]
    _ = _ := by
      simpa only [Real.toNNReal_coe] using PathIntegratedCovariance.clock_before H T hT
        (fun s => Real.exp (s*(2*(n : ℝ)^2))*diagonal G hG hβ hβ1 i a n (U (s.toNNReal,ω)))

/-- Mixed compensators retain the literal fixed white-noise direction. -/
theorem mixed_ae (b : Input (d := d)) : ∀ᵐ ω ∂μ,∀ T : ℝ≥0,T ≤ H →
    NativeCrossCompensator.value (MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEnergy i a n)
      (RotatedCylindricalCoordinates.constant F μ H b) T ω=
      ∫ s in (0 : ℝ)..(T : ℝ),Real.exp (s*(n : ℝ)^2)*
        mixed G hG hβ hβ1 i a n b (U (s.toNNReal,ω)) := by
  let u := MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEnergy i a n
  let v := RotatedCylindricalCoordinates.constant F μ H b
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := PredictableL2.timeMeasure H)).quasiMeasurePreserving.ae
    ((MatrixUnboundedFourierInput.input_ae F μ H G hG hβ hβ1 U hU hEnergy i a n).and
      (RotatedCylindricalCoordinates.constant_ae F μ H b))
  filter_upwards [NativeCrossCompensator.value_ae u v,Measure.ae_ae_of_ae_prod hs] with ω hv hrow T hT
  rw [hv T,timeMeasure_eq]
  rw [timeMeasure_eq] at hrow
  calc
    _ = ∫ s,(Set.Iio T).indicator (fun s : ℝ≥0 => Real.exp ((s : ℝ)*(n : ℝ)^2)*
        mixed G hG hβ hβ1 i a n b (U (s,ω))) s ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
      apply integral_congr_ae
      filter_upwards [hrow] with s hs
      by_cases ht : s < T
      · simp only [Set.indicator_apply,Set.mem_Iio,ht,ite_true]
        dsimp only [Prod.swap] at hs
        change inner ℝ (u (s,ω)) (v (s,ω))=_
        rw [hs.1,hs.2,MatrixUnboundedFourierInput.row,real_inner_smul_left]
        dsimp [FourierHeatInput.multiplier]
        rw [min_eq_left (show (s : ℝ) ≤ H from ht.le.trans hT),mixed_apply]
      · simp only [Set.indicator_apply,Set.mem_Iio,ht,ite_false]
    _ = _ := by
      simpa only [Real.toNNReal_coe] using PathIntegratedCovariance.clock_before H T hT
        (fun s => Real.exp (s*(n : ℝ)^2)*mixed G hG hβ hβ1 i a n b (U (s.toNNReal,ω)))

end SHEStochastic.MatrixUnboundedNativeCompensator
