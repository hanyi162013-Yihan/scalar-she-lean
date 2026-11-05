module

public import SHEStochastic.MatrixPointHeatInput
public import SHE.FullHorizonTargetContinuity
public import SHE.OriginalNativeHeatParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixPointTargetContinuity
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

theorem row_continuousAt {τ : ℝ} (hτ : 0 < τ) (P : Profile d) (x : HeatCircle) (i : d) :
    ContinuousAt (fun r => MatrixPointHeatRows.row r P x i) τ := by
  simp_rw [MatrixPointHeatRows.row_eq]
  apply (factor P).adjoint.continuous.continuousAt.comp
  have h := (OriginalNativeHeatParameterContinuity.test_joint hτ x).comp
    (f := fun r : ℝ => (r,x)) (x := τ) (continuous_id.prodMk continuous_const).continuousAt
  exact ((L2EuclideanCoordinates.injection i).compLpL 2
    (AddCircle.haarAddCircle (T := (1 : ℝ)))).continuous.continuousAt.comp h

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U)
    (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
    (s : ℝ≥0) (hs : s ≤ H)

def process (T : ℝ≥0) (hT : T ≤ H) (x : HeatCircle) (i : d) : Process (E := Input (d := d)) F μ H :=
  StoppedItoInputs.stop F μ H (s : ℝ) (MatrixPointHeatInput.input F μ H hH U hU Q hUpper hQ T hT x i)

theorem process_ae (T : ℝ≥0) (hT : T ≤ H) (x : HeatCircle) (i : d) :
    process F μ H hH U hU Q hUpper hQ s T hT x i =ᵐ[energyMeasure μ H]
      fun p => if (p.1 : ℝ)<(s : ℝ) then MatrixPointHeatRows.row ((T : ℝ)-(p.1 : ℝ)) (Q p) x i else 0 := by
  filter_upwards [StoppedItoInputs.stop_ae F μ H (s : ℝ)
      (MatrixPointHeatInput.input F μ H hH U hU Q hUpper hQ T hT x i),
    MatrixPointHeatInput.input_ae F μ H hH U hU Q hUpper hQ T hT x i] with p hp hrow
  change process F μ H hH U hU Q hUpper hQ s T hT x i p=_ at hp
  rw [hp]
  simp only [StoppedItoInputs.before,Set.indicator_apply,Set.mem_setOf_eq]
  split_ifs
  · exact hrow
  · rfl

theorem process_bound (T : ℝ≥0) (hT : T ≤ H) (hsT : s ≤ T) (x : HeatCircle) (i : d) :
    ∀ᵐ p ∂energyMeasure μ H, ‖process F μ H hH U hU Q hUpper hQ s T hT x i p‖^2 ≤
      FullHorizonTargetContinuity.majorant (M := U) s p := by
  filter_upwards [process_ae F μ H hH U hU Q hUpper hQ s T hT x i] with p hp
  rw [hp]
  by_cases ht : (p.1 : ℝ)<(s : ℝ)
  · simp only [if_pos ht,FullHorizonTargetContinuity.majorant,
      Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) (s : ℝ) from ht)]
    have hpos : 0<(T : ℝ)-(p.1 : ℝ) := sub_pos.mpr (ht.trans_le hsT)
    have he := (MatrixPointHeatRows.norm_sq hpos (Q p) x i).trans
      (mul_le_mul_of_nonneg_right (hUpper p)
        (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg hpos.le _))))
    exact he.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ht)
          (sub_le_sub_right (show (s : ℝ)≤(T : ℝ) from hsT) _) (by norm_num)) heatConstant_pos.le)) hU)
  · simp only [if_neg ht,FullHorizonTargetContinuity.majorant,
      Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) (s : ℝ) from ht),norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),le_refl]

include hs in
/-- Original-target point inputs converge in the same predictable L2
space even when the heat target reaches the stopping time. The existing
integrable square majorant handles the genuine endpoint singularity. -/
theorem tendsto (T : ℝ≥0) (hT : T ≤ H) (hsT : s ≤ T)
    (Tn : ℕ → ℝ≥0) (hTn : ∀ j, Tn j ≤ H) (hsTn : ∀ j, s ≤ Tn j)
    (hlim : Tendsto Tn atTop (𝓝 T)) (x : HeatCircle) (i : d) :
    Tendsto (fun j => process F μ H hH U hU Q hUpper hQ s (Tn j) (hTn j) x i) atTop
      (𝓝 (process F μ H hH U hU Q hUpper hQ s T hT x i)) := by
  apply PredictableSquareDominatedLimit.tendsto F μ H _ _
    (FullHorizonTargetContinuity.majorant (M := U) s)
    (FullHorizonTargetContinuity.majorant_integrable F μ H s hs)
    (fun j => process_bound F μ H hH U hU Q hUpper hQ s (Tn j) (hTn j) (hsTn j) x i)
    (process_bound F μ H hH U hU Q hUpper hQ s T hT hsT x i)
  filter_upwards [ae_all_iff.mpr (fun j => process_ae F μ H hH U hU Q hUpper hQ s (Tn j) (hTn j) x i),
    process_ae F μ H hH U hU Q hUpper hQ s T hT x i] with p hn hp
  rw [hp]
  simp_rw [hn]
  by_cases ht : (p.1 : ℝ)<(s : ℝ)
  · simp only [if_pos ht]
    exact (row_continuousAt (sub_pos.mpr (ht.trans_le hsT)) (Q p) x i).tendsto.comp
      ((NNReal.continuous_coe.tendsto T |>.comp hlim).sub_const (p.1 : ℝ))
  · simp only [if_neg ht]
    exact tendsto_const_nhds

end SHEStochastic.MatrixPointTargetContinuity
