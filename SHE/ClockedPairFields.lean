module

public import SHE.ClockedHaarIntegral
public import SHE.AdditiveResidualPair
public import SHE.DampedIntegralCongruence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ClockedPairFields
open MeasureTheory PredictableTimeDilation LowBands FiniteHaar ContinuousHeatMild
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (c : ℝ≥0) (hc : 0<c)

def path (U : ℝ≥0→Ω→StateL2) (t : ℝ≥0) : Ω→StateL2 := U ((clock c hc).symm t)

theorem path_continuous (U : ℝ≥0→Ω→StateL2) (hU : ∀ ω,Continuous (fun t => U t ω)) (ω : Ω) :
    Continuous (fun t => path c hc U t ω) :=
  (hU ω).comp (clock_symm_continuous c hc)

theorem path_predictable (U : ℝ≥0→Ω→StateL2)
    (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U)) :
    StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable] (Function.uncurry (path c hc U)) :=
  hU.comp_measurable (measurable_backward 𝓕 (clock c hc))

theorem coefficient_predictable {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
    (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
    (hm : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
    (U : ℝ≥0→Ω→StateL2) (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U)) :
    StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable]
      (coefficientFunction ha hell hb (path c hc U)) :=
  (hm.comp (path_predictable 𝓕 c hc U hU).measurable).stronglyMeasurable

/-- Scaling the variance and the Brownian clock uses the same Haar
coordinates, with no change of the additive/residual coupling. -/
theorem unitField_coefficient {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
    (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M) (U : ℝ≥0→Ω→StateL2) :
    ClockedHaarIntegral.unitField c hc (coefficientFunction ha hell hb (path c hc U))=
      coefficientFunction (ha.const_mul (c:ℝ)) (mul_pos hc hell)
        (HaarFieldScaling.scaled_bounds hc hb) U := by
  funext p
  simp only [ClockedHaarIntegral.unitField,coefficientFunction,path,OrderIso.symm_apply_apply]
  exact (HaarFieldScaling.coefficientField_scale ha hell hb (c:ℝ) hc (U p.1 p.2)).symm

theorem constantField_scale (κ : ℝ) (hκ : 0<κ) :
    HaarFieldScaling.scale (c:ℝ) hc (AdditiveHaarForcing.constantField κ hκ)=
      AdditiveHaarForcing.constantField ((c:ℝ)*κ) (mul_pos hc hκ) := by
  exact (HaarFieldScaling.coefficientField_scale measurable_const hκ
    (fun _ => ⟨le_rfl,le_rfl⟩) (c:ℝ) hc 0).symm

theorem unitField_constant (κ : ℝ) (hκ : 0<κ) :
    ClockedHaarIntegral.unitField c hc (fun _ : ℝ≥0×Ω => AdditiveHaarForcing.constantField κ hκ)=
      fun _ => AdditiveHaarForcing.constantField ((c:ℝ)*κ) (mul_pos hc hκ) := by
  funext p
  exact constantField_scale c hc κ hκ

end SHE.ClockedPairFields
