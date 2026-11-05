module

public import SHEStochastic.CanonicalFourierFluctuation
public import SHE.CanonicalStateDriverPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.CanonicalLinearFluctuation
open MeasureTheory SHE SHE.PredictableL2 StoppedPathPasting
open scoped NNReal ENNReal
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Countable ι] [DecidableEq ι]
    (H : ℝ≥0) (L : E →L[ℝ] ℝ) (rate : ℝ)
abbrev Space := CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H

/-- Integrating-factor fluctuation of a continuous linear state coordinate. -/
def value (t : ℝ≥0) (x : Space (E := E) (ι := ι) H) : ℝ :=
  Real.exp ((min t H : ℝ≥0)*rate)*L (x.1 (CanonicalStateDriverFiltration.clock H t))-L (x.1 (origin H))

theorem continuous (t : ℝ≥0) : Continuous (value (ι := ι) H L rate t) :=
  (continuous_const.mul (L.continuous.comp ((continuous_eval_const _).comp continuous_fst))).sub
    (L.continuous.comp ((continuous_eval_const _).comp continuous_fst))

/-- Time continuity is independent of the selected state coordinate. -/
theorem time (x : Space (E := E) (ι := ι) H) :
    Continuous (fun t => value H L rate t x) := by
  change Continuous (fun t : ℝ≥0 => Real.exp ((min t H : ℝ≥0)*rate)*
    L (CanonicalStateDriverFiltration.state H t x)-L (x.1 (origin H)))
  simp only [NNReal.coe_min]
  exact ((Real.continuous_exp.comp ((continuous_subtype_val.min continuous_const).mul_const rate)).mul
    (L.continuous.comp (CanonicalStateDriverFiltration.state_continuous H x))).sub continuous_const

theorem clip (t : ℝ≥0) : value (ι := ι) H L rate t=value H L rate (min t H) := by
  funext x
  simp [value,CanonicalStateDriverFiltration.clock,NNReal.coe_min,min_assoc,min_self]

theorem adapted : StronglyAdapted (CanonicalStateDriverFiltration.filtration H)
    (value (ι := ι) H L rate) := by
  intro t
  let F := CanonicalStateDriverFiltration.filtration (E := E) (ι := ι) H
  have ht := (JointCanonicalCylinderRecognition.adapted (E := E) (ι := ι) H
    (AdaptedCanonicalPathTests.clock H t)).mono
      (F.mono (show AdaptedCanonicalPathTests.toNN H (AdaptedCanonicalPathTests.clock H t) ≤ t
        from min_le_left _ _)) le_rfl
  have h0 := (JointCanonicalCylinderRecognition.adapted (E := E) (ι := ι) H (origin H)).mono
    (F.mono (show AdaptedCanonicalPathTests.toNN H (origin H) ≤ t from zero_le)) le_rfl
  exact (stronglyMeasurable_const.mul (L.continuous.comp_stronglyMeasurable ht.fst.stronglyMeasurable)).sub
    (L.continuous.comp_stronglyMeasurable h0.fst.stronglyMeasurable)

theorem zero (x : Space (E := E) (ι := ι) H) : value H L rate 0 x=0 := by
  simp [value,CanonicalStateDriverFiltration.clock,origin]

theorem comp_bundle {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : FiniteScalarIto.Family F μ H ι) (W : ℝ≥0 → Ω → E)
    (hcW : ∀ ω,Continuous (fun t => W t ω)) (t : ℝ≥0) (ω : Ω) :
    value H L rate t (CanonicalNativeBrownian.bundle F μ H P W hcW ω)=
      Real.exp ((min t H : ℝ≥0)*rate)*L (W (min t H) ω)-L (W 0 ω) := by
  change Real.exp ((min t H : ℝ≥0)*rate)*L
    (W (0+(CanonicalStateDriverFiltration.clock H t).val.toNNReal) ω)-
      L (W (0+(origin H).val.toNNReal) ω)=_
  rw [CanonicalFourierFluctuation.clock_time H t]
  simp only [zero_add,origin,Real.toNNReal_zero]

end SHEStochastic.CanonicalLinearFluctuation
