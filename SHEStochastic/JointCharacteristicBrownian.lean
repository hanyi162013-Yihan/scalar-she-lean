module

public import SHEStochastic.JointPathFiltration
public import SHEStochastic.ReferenceBrownianRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.JointCharacteristicBrownian
open MeasureTheory ProbabilityTheory SHE
open StoppedPathPasting AdaptedCanonicalPathTests JointPathFiltration
open scoped NNReal InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Countable ι] [DecidableEq ι] (H : ℝ≥0)

theorem value_eq {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n)
    (q : ℝ≥0) (x : Space (E := E) (ι := ι) H) :
    PastedCharacteristicFunctional.value H (JointDriverCharacteristic.row (V := E) a r)
      (GaussianCharacteristicMartingale.variance a r) x (clock H q) =
      Complex.exp
        (((FiniteCharacteristicRecognition.phase (driver (E := E) H) a r (min q H) x-
          FiniteCharacteristicRecognition.phase (driver (E := E) H) a r 0 x : ℝ) : ℂ)*Complex.I +
            (GaussianCharacteristicMartingale.variance a r * (min q H : ℝ≥0) : ℝ)) := by
  have hclock : clock H (min q H) = clock H q := by
    apply Subtype.ext
    simp only [clock, NNReal.coe_min, min_assoc, min_self]
  have hz : FiniteCharacteristicRecognition.phase (driver (E := E) H) a r 0 x = 0 := by
    simp only [FiniteCharacteristicRecognition.phase, driver_zero]
    exact inner_zero_left r
  have hr : JointDriverCharacteristic.row (V := E) a r (x (clock H q)-x (origin H)) =
      FiniteCharacteristicRecognition.phase (driver (E := E) H) a r (min q H) x := by
    rw [JointDriverCharacteristic.row_apply, FiniteCharacteristicRecognition.phase]
    congr 1
    apply PiLp.ext
    intro i
    change (x (clock H q)).2 (a i)-(x (origin H)).2 (a i) =
      (x (clock H (min q H))).2 (a i)-(x (origin H)).2 (a i)
    rw [hclock]
  rw [PastedCharacteristicFunctional.value, hr, hz, sub_zero]
  rfl

variable [TopologicalSpace.MetrizableSpace (Space (E := E) (ι := ι) H)]
  (ν : Measure (Space (E := E) (ι := ι) H)) [IsProbabilityMeasure ν]
  {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (P : FiniteScalarIto.Family F μ H ι)

/-- All characteristic identities produce the complete Brownian family
on the full joint canonical filtration. The reference family is the
already supplied original driver, and contributes no extra assumption. -/
def family
    (hId : ∀ n (a : Fin n → ι) (r : WordRecursion.State n),
      PastedCharacteristicMartingale.Identity H (JointDriverCharacteristic.row (V := E) a r)
        (GaussianCharacteristicMartingale.variance a r) ν) :
    FiniteScalarIto.Family (filtration (E := E) (ι := ι) H) ν H ι := by
  apply ReferenceBrownianRecognition.family (filtration H) ν H (driver H) F μ P
    (driver_adapted H) (driver_continuous H)
    (fun i ↦ Filter.Eventually.of_forall (driver_zero H i))
  intro n a r
  have hh := PastedCharacteristicMartingale.martingale H
    (JointDriverCharacteristic.row (V := E) a r) (GaussianCharacteristicMartingale.variance a r) ν
    (filtration H) (GaussianCharacteristicMartingale.variance_nonneg a r)
    (evaluation_adapted H) (fun _ ↦ le_rfl) (hId n a r)
  convert hh using 1
  funext q x
  exact (value_eq H a r q x).symm

end SHEStochastic.JointCharacteristicBrownian
