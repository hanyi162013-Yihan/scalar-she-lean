module

public import SHE.CircleMultiplier
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.CircleMultiplier

open MeasureTheory AddCircle CircleHeat FiniteHaar
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem scalar_real_inner_symmetric (c v w : ℂ) (hc : c.im = 0) :
    inner ℂ (c * v) w = inner ℂ v (c * w) := by
  have hconj : (starRingEnd ℂ) c = c := by apply Complex.ext <;> simp [hc]
  simp only [RCLike.inner_apply, map_mul, hconj]
  ring

theorem operator_inner_symmetric (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0) (v w : CircleL2) :
    inner ℂ (operator c U hc v) w = inner ℂ v (operator c U hc w) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae c U hc v, operator_ae c U hc w, hcReal] with y hv hw hr
  rw [hv, hw]
  exact scalar_real_inner_symmetric _ _ _ hr

theorem operator_adjoint (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0) : (operator c U hc).adjoint = operator c U hc := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, operator_inner_symmetric c U hc hcReal]

theorem rootMemLp (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) :
    MemLp (fun y => (Real.sqrt (c y).re : ℂ)) 2 haarAddCircle := by
  have hcont : Continuous (fun z : ℂ => (Real.sqrt z.re : ℂ)) := by fun_prop
  apply MemLp.of_bound (hcont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable c)) (Real.sqrt U)
  filter_upwards [hc] with y hy
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hy

def rootCoefficient (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) : CircleL2 := (rootMemLp c U hc).toLp _

theorem rootCoefficient_ae (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) :
    ⇑(rootCoefficient c U hc) =ᵐ[haarAddCircle] fun y => (Real.sqrt (c y).re : ℂ) :=
  (rootMemLp c U hc).coeFn_toLp

theorem rootCoefficient_real (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) :
    ∀ᵐ y ∂haarAddCircle, (rootCoefficient c U hc y).im = 0 := by
  filter_upwards [rootCoefficient_ae c U hc] with y hy
  simp [hy]

theorem rootCoefficient_norm_bound (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) :
    ∀ᵐ y ∂haarAddCircle, ‖rootCoefficient c U hc y‖ ≤ Real.sqrt U := by
  filter_upwards [rootCoefficient_ae c U hc, hc] with y hy hb
  rw [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hb

theorem rootCoefficient_lower_bound (c : CircleL2) (m U : ℝ)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) :
    ∀ᵐ y ∂haarAddCircle, Real.sqrt m ≤ (rootCoefficient c U hcu y).re := by
  filter_upwards [rootCoefficient_ae c U hcu, hcl] with y hy hb
  rw [hy, Complex.ofReal_re]
  exact Real.sqrt_le_sqrt hb

theorem rootCoefficient_square (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) :
    ∀ᵐ y ∂haarAddCircle, rootCoefficient c U hcu y * rootCoefficient c U hcu y = c y := by
  filter_upwards [rootCoefficient_ae c U hcu, hcReal, hcl] with y hy hr hl
  rw [hy, ← Complex.ofReal_mul]
  have hs : Real.sqrt (c y).re * Real.sqrt (c y).re = (c y).re :=
    by simpa only [pow_two] using Real.sq_sqrt (hm.trans_le hl).le
  rw [hs]
  apply Complex.ext <;> simp [hr]

def rootEquivalence (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U) : CircleL2 ≃L[ℂ] CircleL2 :=
  equivalence (rootCoefficient c U hcu) (Real.sqrt m) (Real.sqrt U) (Real.sqrt_pos.mpr hm)
    (rootCoefficient_lower_bound c m U hcl hcu) (rootCoefficient_norm_bound c U hcu)

theorem rootEquivalence_covariance (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, (c y).re ≤ U)
    (hcNorm : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) :
    (rootEquivalence c m U hm hcl hcu).toContinuousLinearMap.comp
      (rootEquivalence c m U hm hcl hcu).toContinuousLinearMap.adjoint = operator c U hcNorm := by
  change (operator (rootCoefficient c U hcu) (Real.sqrt U) (rootCoefficient_norm_bound c U hcu)).comp
    (operator (rootCoefficient c U hcu) (Real.sqrt U) (rootCoefficient_norm_bound c U hcu)).adjoint = _
  rw [operator_adjoint _ _ _ (rootCoefficient_real c U hcu)]
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [operator_ae (rootCoefficient c U hcu) (Real.sqrt U) (rootCoefficient_norm_bound c U hcu)
      (operator (rootCoefficient c U hcu) (Real.sqrt U) (rootCoefficient_norm_bound c U hcu) v),
    operator_ae (rootCoefficient c U hcu) (Real.sqrt U) (rootCoefficient_norm_bound c U hcu) v,
    operator_ae c U hcNorm v, rootCoefficient_square c m U hm hcReal hcl hcu] with y ha hb hc hs
  change operator (rootCoefficient c U hcu) (Real.sqrt U) (rootCoefficient_norm_bound c U hcu)
    (operator (rootCoefficient c U hcu) (Real.sqrt U) (rootCoefficient_norm_bound c U hcu) v) y = operator c U hcNorm v y
  rw [ha, hb, hc, ← mul_assoc, hs]

end SHE.CircleMultiplier
