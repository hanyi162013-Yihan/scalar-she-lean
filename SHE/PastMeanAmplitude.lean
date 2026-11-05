module

public import SHE.PastWordTimeFields
public import SHE.HistoryQuarterFields
public import SHE.UniformPhysicalScoreForest
public import SHE.AllDataDecayFreshScore

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanAmplitude
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- Exact deterministic amplitude after replacing all random old scores
by their common parent forest. It keeps the actual relative-age word
sum and the literal stop-weight damping at the later quarter row. -/
def value (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (q A0 ν : ℝ) (p : History X k) : ℝ :=
  max (timeWeight L (ControlledOldIntervals.fraction P*P.lower) (uniformConstant n) k p) 0*
    sqrt (2*UniformFutureProfileScores.constant (n+k)/(P.lower*
      ((carrier L k).terminal p-HistoryQuarterFields.rowTime L k q p)))*
      PastWordTimeFields.total L P k p A0 ν

/-- The damping parameter is independent of the current law time. -/
def damped (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (Λ q A0 ν : ℝ) (p : History X k) : ℝ :=
  exp (-Λ*(HistoryQuarterFields.rowTime L k q p-q))*value L P k q A0 ν p

theorem value_nonneg (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (q A0 ν : ℝ) (p : History X k) :
    0≤value L P k q A0 ν p := by
  unfold value
  exact mul_nonneg (mul_nonneg (le_max_right _ _) (sqrt_nonneg _))
    (PastWordTimeFields.total_nonneg L P k p A0 ν)

theorem damped_nonneg (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (Λ q A0 ν : ℝ) (p : History X k) :
    0≤damped L P k Λ q A0 ν p := mul_nonneg (exp_pos _).le (value_nonneg L P k q A0 ν p)

theorem value_measurable (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (q A0 ν : ℝ) :
    Measurable (value L P k q A0 ν) := by
  unfold value
  exact (((FixedHistoryTimeFactors.timeWeight_measurable L _ _ k).max measurable_const).mul
    (Real.continuous_sqrt.measurable.comp (measurable_const.div
      (((carrier L k).terminal_measurable.sub (HistoryQuarterFields.rowTime_measurable L k q)).const_mul P.lower)))).mul
        (PastWordTimeFields.total_measurable L P k A0 ν)

theorem damped_measurable (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (Λ q A0 ν : ℝ) :
    Measurable (damped L P k Λ q A0 ν) :=
  (((HistoryQuarterFields.rowTime_measurable L k q).sub_const q).const_mul (-Λ)).exp.mul
    (value_measurable L P k q A0 ν)

theorem value_replaceSpace (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (q A0 ν : ℝ)
    (p : History X k) (x : Fin k→HeatCircle) :
    value L P k q A0 ν (replaceSpace k p x)=value L P k q A0 ν p := by
  simp only [value,timeWeight_replaceSpace,replaceSpace_terminal,HistoryQuarterFields.rowTime_replaceSpace,
    PastWordTimeFields.total_replaceSpace]

theorem damped_replaceSpace (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (Λ q A0 ν : ℝ)
    (p : History X k) (x : Fin k→HeatCircle) :
    damped L P k Λ q A0 ν (replaceSpace k p x)=damped L P k Λ q A0 ν p := by
  simp only [damped,value_replaceSpace,HistoryQuarterFields.rowTime_replaceSpace]

end SHE.PastMeanAmplitude
