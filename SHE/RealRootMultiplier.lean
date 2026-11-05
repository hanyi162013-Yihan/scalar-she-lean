module
public import SHE.HaarPhysicalAnalysis
public import SHE.ScalarSplittingInputs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.RealRootMultiplier
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M)

def action (v : RealL2) : RealL2 :=
  realPart (CircleMultiplier.rootEquivalence f.1 ell M hell
    (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2)) (realEmbed v))

/-- The real restriction of the actual positive square-root multiplier
has its literal pointwise coefficient. -/
theorem action_ae (v : RealL2) :
    action hell f v =ᵐ[haarAddCircle] fun y => Real.sqrt (f.1 y).re * v y := by
  have hp := Complex.reCLM.coeFn_compLpL (p:=2)
    (CircleMultiplier.rootEquivalence f.1 ell M hell
      (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2)) (realEmbed v))
  have hop := CircleMultiplier.operator_ae
    (CircleMultiplier.rootCoefficient f.1 M (f.2.2.mono (fun _ h => h.2))) (Real.sqrt M)
    (CircleMultiplier.rootCoefficient_norm_bound f.1 M _) (realEmbed v)
  filter_upwards [hp,hop,CircleMultiplier.rootCoefficient_ae f.1 M
    (f.2.2.mono (fun _ h => h.2)),realEmbed_ae v] with y hp ho hr hv
  change action hell f v y = _ at hp
  change action hell f v y = _
  rw [hp]
  change (CircleMultiplier.operator
    (CircleMultiplier.rootCoefficient f.1 M (f.2.2.mono (fun _ h => h.2))) (Real.sqrt M)
    (CircleMultiplier.rootCoefficient_norm_bound f.1 M _) (realEmbed v) y).re = _
  rw [ho,hr,hv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

/-- The residual covariance field produces exactly the scalar physical
input required by the ordinary two-noise splitting. -/
theorem residual_input
    (g : UnitAddCircle → ℝ) (hg : AEStronglyMeasurable g haarAddCircle)
    (m C : ℝ) (hbound : ∀ᵐy∂haarAddCircle, |g y| ≤ C)
    (hf : ∀ᵐy∂haarAddCircle, (f.1 y).re = (g y)^2-m^2)
    (v : RealL2) :
    action hell f v = ScalarSplittingInputs.residualInput haarAddCircle g hg m C hbound v := by
  apply Lp.ext
  filter_upwards [action_ae hell f v,hf,
    RealMultiplier.operator_ae haarAddCircle (fun y => Real.sqrt ((g y)^2-m^2))
      (ScalarSplittingInputs.root_measurable haarAddCircle g hg m) |C|
      (ScalarSplittingInputs.root_bound haarAddCircle g m C hbound) v] with y ha hf hr
  rw [ha,hf]
  exact hr.symm

/-- Exact physical decoding of an original common-Haar analysis row. -/
theorem decode_analysis (v : RealL2) :
    (fieldRealInnovation ell M hell f).symm
      (realInputPart (factorAnalysis f.1 ell M hell f.2.1 f.2.2 (realEmbed v))) =
      action hell f v := by
  rw [realFactorAnalysis_innovation,LinearIsometryEquiv.symm_apply_apply]
  rfl
end SHE.RealRootMultiplier
