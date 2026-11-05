module

public import SHEStochastic.VectorAnalyticHeat
public import SHEStochastic.MatrixFixedHaarInput
public import SHE.NativeSignedClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixAnalyticKernel
open MeasureTheory SHE SHE.FiniteHaar SHE.StoppedFourier MatrixInfiniteHaar NativeHeatObservation
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology

def kernel (t : ℝ) (P : Profile d) : MatrixHaarKernel.Columns (d := d) :=
  MatrixHaarKernel.kernel (t/timeScale) P

theorem column (t : ℝ) (P : Profile d) (k : d × HaarNode) :
    kernel t P k=if 0 < t then VectorAnalyticHeat.heat t (factor P (lp.single 2 k 1)) else 0 := by
  rw [kernel,MatrixHaarKernel.column]
  simp only [div_pos_iff_of_pos_right timeScale_pos,VectorAnalyticHeat.heat]

theorem zero {t : ℝ} (ht : t ≤ 0) (P : Profile d) : kernel t P=0 :=
  MatrixFixedHaarInput.kernel_zero (div_nonpos_of_nonpos_of_nonneg ht timeScale_pos.le) P

def constant (d : Type*) [Fintype d] (U : ℝ) : ℝ :=
  MatrixFixedHaarInput.constant d U*timeScale^(1/2 : ℝ)

theorem constant_nonneg {U : ℝ} (hU : 0 ≤ U) : 0 ≤ constant d U :=
  mul_nonneg (MatrixFixedHaarInput.constant_nonneg hU) (Real.rpow_nonneg timeScale_pos.le _)

theorem constant_mono {U V : ℝ} (hUV : U ≤ V) : constant d U ≤ constant d V :=
  mul_le_mul_of_nonneg_right (MatrixFixedHaarInput.constant_mono hUV)
    (Real.rpow_nonneg timeScale_pos.le _)

theorem small_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (P : Profile d) :
    ‖kernel t P‖^2 ≤ constant d P.upper*t^(-(1/2 : ℝ)) := by
  have hc : 1 ≤ timeScale := by unfold timeScale; nlinarith [Real.one_le_pi_div_two]
  have hb := MatrixFixedHaarInput.small_bound (div_pos ht timeScale_pos)
    ((div_le_one timeScale_pos).mpr (ht1.trans hc)) P
  rw [NativeSignedClock.div_neg_rpow ht.le] at hb
  exact hb.trans_eq (by unfold constant; ring)

def gapConstant (d : Type*) [Fintype d] (U δ : ℝ) : ℝ :=
  (Fintype.card d : ℝ)*U*(1+2*HeatTrace.fractionalGaussianIntegral 0*
    (δ/timeScale)^(-(1/2 : ℝ)))

theorem gapConstant_nonneg {U δ : ℝ} (hU : 0 ≤ U) (hδ : 0 < δ) : 0 ≤ gapConstant d U δ := by
  have hG := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ) < 1/2)).le
  unfold gapConstant
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hU)
    (add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num) hG)
      (Real.rpow_nonneg (div_nonneg hδ.le timeScale_pos.le) _)))

/-- A positive deterministic observation gap bounds every stopped cell,
including cells whose right endpoint extends beyond the final horizon. -/
theorem gap_bound {t δ U : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (P : Profile d) (hU : P.upper ≤ U) :
    ‖kernel t P‖^2 ≤ gapConstant d U δ := by
  have ht : 0 < t := hδ.trans_le hδt
  have hG : 0 ≤ 2*HeatTrace.fractionalGaussianIntegral 0 :=
    mul_nonneg (by norm_num) (HeatTrace.fractionalGaussianIntegral_pos (by norm_num)).le
  have hp := Real.rpow_le_rpow_of_nonpos (div_pos hδ timeScale_pos)
    (div_le_div_of_nonneg_right hδt timeScale_pos.le) (by norm_num : -(1/2 : ℝ) ≤ 0)
  have hb := MatrixHaarKernel.norm_sq (div_pos ht timeScale_pos) P
  have he := mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hp hG) 1)
    (mul_nonneg (Nat.cast_nonneg (Fintype.card d)) P.upper_pos.le)
  have hcap : (Fintype.card d : ℝ)*P.upper*
      (1+2*HeatTrace.fractionalGaussianIntegral 0*(δ/timeScale)^(-(1/2 : ℝ))) ≤
      (Fintype.card d : ℝ)*U*
      (1+2*HeatTrace.fractionalGaussianIntegral 0*(δ/timeScale)^(-(1/2 : ℝ))) := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg (Fintype.card d)))
    (add_nonneg zero_le_one (mul_nonneg hG (Real.rpow_nonneg (div_nonneg hδ.le timeScale_pos.le) _)))
  exact hb.trans (he.trans hcap)

local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩

theorem measurable {Z : Type*} [MeasurableSpace Z] (τ : Z → ℝ) (hτ : Measurable τ)
    (Q : Z → Profile d)
    (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2)) :
    Measurable (fun z => kernel (τ z) (Q z)) :=
  MatrixHaarKernel.measurable _ (hτ.div_const timeScale) Q hQ

theorem predictable {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (Q : ℝ≥0 × Ω → Profile d)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2)) (t : ℝ) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => kernel (t-(p.1 : ℝ)) (Q p)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (measurable _ (measurable_const.sub (PredictableClock.real_time_measurable F)) Q hQ).stronglyMeasurable

end SHEStochastic.MatrixAnalyticKernel
