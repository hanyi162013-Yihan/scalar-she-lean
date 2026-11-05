module

public import SHEStochastic.MatrixAnalyticKernel
public import SHEStochastic.CausalKernelInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixFiniteHorizonKernel
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0  <  (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology

def constant (L U : ℝ) : ℝ := MatrixAnalyticKernel.constant d U+
  MatrixAnalyticKernel.gapConstant d U 1*(max 1 L)^(1/2 : ℝ)

theorem constant_nonneg {L U : ℝ} (hU : 0 ≤ U) : 0 ≤ constant (d := d) L U :=
  add_nonneg (MatrixAnalyticKernel.constant_nonneg hU)
    (mul_nonneg (MatrixAnalyticKernel.gapConstant_nonneg hU zero_lt_one) (Real.rpow_nonneg (le_max_left 1 L |>.trans' zero_le_one) _))

/-- The actual analytic matrix Haar kernel has the same integrable
heat singularity on every finite horizon. Large ages use the existing
positive-gap estimate; no new heat or stochastic input is assumed. -/
theorem bound {t L U : ℝ} (ht : 0 < t) (htL : t ≤ L) (hU : 0 ≤ U)
    (P : Profile d) (hcap : P.upper ≤ U) :
    ‖MatrixAnalyticKernel.kernel t P‖^2 ≤ constant (d := d) L U*t^(-(1/2 : ℝ)) := by
  have hgap := MatrixAnalyticKernel.gapConstant_nonneg (d := d) hU zero_lt_one
  have hmax : 0 < max (1 : ℝ) L := zero_lt_one.trans_le (le_max_left _ _)
  have hlarge : 0 ≤ MatrixAnalyticKernel.gapConstant d U 1*(max 1 L)^(1/2 : ℝ) :=
    mul_nonneg hgap (Real.rpow_nonneg hmax.le _)
  have hsmall := MatrixAnalyticKernel.constant_nonneg (d := d) hU
  have hp : 0 ≤ t^(-(1/2 : ℝ)) := Real.rpow_nonneg ht.le _
  by_cases ht1 : t ≤ 1
  · calc
      _  ≤  MatrixAnalyticKernel.constant d P.upper*t^(-(1/2 : ℝ)) := MatrixAnalyticKernel.small_bound ht ht1 P
      _  ≤  MatrixAnalyticKernel.constant d U*t^(-(1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (MatrixAnalyticKernel.constant_mono hcap) hp
      _  ≤  _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hlarge) hp
  · have hpow : (max (1 : ℝ) L)^(-(1/2 : ℝ)) ≤ t^(-(1/2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht (htL.trans (le_max_right _ _)) (by norm_num)
    have he : (max (1 : ℝ) L)^(1/2 : ℝ)*(max 1 L)^(-(1/2 : ℝ))=1 := by
      rw [←Real.rpow_add hmax]
      norm_num
    calc
      _  ≤  MatrixAnalyticKernel.gapConstant d U 1 :=
        MatrixAnalyticKernel.gap_bound zero_lt_one (le_of_not_ge ht1) P hcap
      _ = (MatrixAnalyticKernel.gapConstant d U 1*(max 1 L)^(1/2 : ℝ))*(max 1 L)^(-(1/2 : ℝ)) := by
        rw [mul_assoc,he,mul_one]
      _  ≤  (MatrixAnalyticKernel.gapConstant d U 1*(max 1 L)^(1/2 : ℝ))*t^(-(1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hlarge
      _  ≤  _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hsmall) hp

variable {Ω : Type*} [MeasurableSpace Ω]
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (cap : ℝ) (hcap : 0 ≤ cap)
    (Q : ℝ≥0×Ω → Profile d) (hUpper : ∀ p,(Q p).upper ≤ cap)
    (hQ : @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

include hcap hUpper hQ in
theorem memLp (t : ℝ≥0) (ht : t ≤ H) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0×Ω => MatrixAnalyticKernel.kernel ((t : ℝ)-(p.1 : ℝ)) (Q p)) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) :=
  CausalKernelInput.memLp_upto H F μ H le_rfl (fun τ p => MatrixAnalyticKernel.kernel τ (Q p))
    (fun τ hτ p => MatrixAnalyticKernel.zero hτ (Q p)) (constant (d := d) H cap) (constant_nonneg hcap)
    (fun τ hτ hτH p => bound hτ hτH hcap (Q p) (hUpper p)) t ht (MatrixAnalyticKernel.predictable F Q hQ t)

def input (t : ℝ≥0) (ht : t ≤ H) : Process (E := MatrixHaarKernel.Columns (d := d)) F μ H :=
  (memLp F μ H cap hcap Q hUpper hQ t ht).toLp _

theorem input_ae (t : ℝ≥0) (ht : t ≤ H) :
    input F μ H cap hcap Q hUpper hQ t ht =ᵐ[energyMeasure μ H]
      fun p : ℝ≥0×Ω => MatrixAnalyticKernel.kernel ((t : ℝ)-(p.1 : ℝ)) (Q p) :=
  ae_eq_of_ae_eq_trim (memLp F μ H cap hcap Q hUpper hQ t ht).coeFn_toLp

end SHEStochastic.MatrixFiniteHorizonKernel
