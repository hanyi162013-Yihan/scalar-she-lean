module

public import SHE.QuarterRMSOldTime
public import SHE.StrictHistoryFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SHE.QuarterRMSTimeFactors
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope
  QuarterSpatialEvent NormalizedKernelSplit RawTraceTimeEnvelope PhysicalAssignmentGapScale
  GaussianAssignmentBlocks AllocatedAssignmentKernel CoveredHistoryGeometry PhysicalParentGeometry
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

/-- All assigned differences are old differences. Their exact minimum
gaps and the untouched full native ages are independent of current q. -/
theorem sharp_total_time_independent (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (k : ℕ) (p : History X k) (q r A0 ν : ℝ) :
    SharpWordTimeScale.total L Q k p q A0 ν=SharpWordTimeScale.total L Q k p r A0 ν := by
  unfold SharpWordTimeScale.total
  congr 1
  apply List.map_congr_left
  intro cs _
  rw [physical_factor_eq L Q k p q A0 ν cs,physical_factor_eq L Q k p r A0 ν cs]

theorem sharp_total_joint_measurable (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (k : ℕ) (A0 ν : ℝ) :
    Measurable (fun z : ℝ × History X k => SharpWordTimeScale.total L Q k z.2 z.1 A0 ν) := by
  have hh := (SharpWordTimeScale.total_measurable L Q k 0 A0 ν).comp
    (measurable_snd : Measurable (Prod.snd : ℝ × History X k → History X k))
  convert! hh using 1
  funext z
  exact sharp_total_time_independent L Q k z.2 z.1 0 A0 ν

theorem totalIntegrand_joint_measurable (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (Cs : ℕ→ℝ) (k : ℕ) (fresh A0 ν : ℝ) :
    Measurable (fun z : ℝ × History X k => totalIntegrand L Q ell Cs k z.1 fresh A0 ν z.2) := by
  classical
  have ha : MeasurableSet {z : ℝ × History X k | StrictHistory L k z.2 ∧
      z.1<(carrier L k).terminal z.2} :=
    ((strictHistory_measurableSet L k).preimage measurable_snd).inter
      (measurableSet_lt measurable_fst ((carrier L k).terminal_measurable.comp measurable_snd))
  have hv := (((carrier L k).terminal_measurable.comp measurable_snd).sub measurable_fst).pow_const (fresh-1)
  have hprod := ((FixedHistoryTimeFactors.timeWeight_measurable L ell Cs k).comp measurable_snd).mul
    (sharp_total_joint_measurable L Q k A0 ν)
  exact (hv.mul hprod).ite ha measurable_const

variable (L : Level R HeatCircle 1)

/-- Joint current-time/old-time Borel RMS envelope, before any AE time
sections are chosen. This is the applicability needed by Hilbert Minkowski. -/
theorem rmsEnvelope_joint_measurable (Q : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (Cs : ℕ→ℝ) (k : ℕ) (A A0 ν J ρ η cutoff Cf U C lam tail : ℝ)
    (E : ℝ→ℝ) (hE : Measurable E) :
    Measurable (fun z : ℝ × (Fin k→ℝ) =>
      rmsEnvelope L Q ell Cs k z.1 A0 ν J ρ η cutoff Cf (A-z.1) U C lam tail (E z.1) z.2) := by
  have hp : Measurable (fun z : ℝ × (Fin k→ℝ) => (z.1,anchor k z.2)) :=
    measurable_fst.prodMk ((anchor_measurable k).comp measurable_snd)
  have hg := (totalIntegrand_joint_measurable L Q ell Cs k (freshDegree ρ η) A0 ν).comp hp
  have hb := (totalIntegrand_joint_measurable L Q ell Cs k (1/2:ℝ) A0 ν).comp hp
  have hG : Measurable (fun z : ℝ × (Fin k→ℝ) => goodTimeFactor J ρ η cutoff k Cf ell (A-z.1)) := by
    unfold goodTimeFactor goodAmplitude
    exact ((measurable_const.mul ((measurable_const.sub measurable_fst).pow_const ((ρ+η)/2))).mul_const _)
  exact ((hG.mul (Real.continuous_sqrt.measurable.comp (hE.comp measurable_fst))).mul hg).add
    (measurable_const.mul hb)

end SHE.QuarterRMSTimeFactors
