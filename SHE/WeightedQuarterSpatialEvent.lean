module

public import SHE.WeightedJointSpatialMoments
public import SHE.QuarterSpatialEvent
public import SHE.SharpTimeSections
public import SHE.FixedHistoryDomain
public import SHE.QuarterHeatNormalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.WeightedQuarterSpatialEvent
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure ActualMeanKernel
  ScalarMeanEnvelope NormalizedKernelSplit QuarterSpatialEvent
local instance weightedQuarterSpatialEvent_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

def timeMoment (μ : Measure Ω) (T Λ : ℝ) (k : ℕ) (q : ℝ)
    (m : Ω → History HeatCircle k → WordRecursion.State (1+k)) (N : ℕ)
    (z : (Fin k → ℝ) × Space) : ℝ :=
  ∫ ω,‖weightedSpatial L k Λ q (quarterRowTime (R:=R) T k q z.1) m z.1 ω z.2.1 z.2.2‖^N ∂μ

/-- The actual post-old-space moment is jointly Borel in ALL remaining
old times and physical input/output coordinates. This event, rather than
a family of chosen time sections, is used in the next Fubini step. -/
theorem timeMoment_measurable (μ : Measure Ω) [SFinite μ] (T Λ : ℝ) (k : ℕ) (q : ℝ)
    (m : Ω → History HeatCircle k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2)) (N : ℕ) :
    Measurable (timeMoment L μ T Λ k q m N) := by
  let M : (Ω × (Fin k → ℝ)) → History HeatCircle k → WordRecursion.State (1+k) :=
    fun z p => m z.1 p
  have hM : Measurable (fun z : (Ω × (Fin k → ℝ)) × History HeatCircle k => M z.1 z.2) :=
    hm.comp (measurable_fst.fst.prodMk measurable_snd)
  have hr : Measurable (fun z : Ω × (Fin k → ℝ) => quarterRowTime (R:=R) T k q z.2) :=
    quarterRowTime_measurable T k measurable_const measurable_snd
  have hh := weightedSpatial_variable_measurable L k Λ (fun _ : Ω × (Fin k → ℝ) => q)
    (fun z => quarterRowTime (R:=R) T k q z.2) measurable_const hr M hM Prod.snd measurable_snd
  have hp : Measurable (fun z : ((Fin k → ℝ) × Space) × Ω => ((z.2,z.1.1),z.1.2)) :=
    (measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd
  have hnorm : Measurable (fun z : ((Fin k → ℝ) × Space) × Ω =>
      ‖weightedSpatial L k Λ q (quarterRowTime (R:=R) T k q z.1.1) m z.1.1 z.2 z.1.2.1 z.1.2.2‖^N) :=
    (hh.comp hp).norm.pow_const N
  exact (hnorm.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable

theorem moment_event_measurableSet (μ : Measure Ω) [SFinite μ]
    (T A Λ : ℝ) (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν C : ℝ)
    (Cs : ℕ → ℝ) (m : Ω → History HeatCircle k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2)) (N : ℕ) :
    MeasurableSet {z : (Fin k → ℝ) × Space | active L T k q z.1 →
      timeMoment L μ T Λ k q m N z ≤
        C*(heatEnvelope (amplitude L Q k q Cf ell A0 ν Cs z.1)
          (quarterTraceTime (R:=R) T k q z.1) (A-q) z.2)^N} := by
  have ha : MeasurableSet {z : (Fin k → ℝ) × Space | active L T k q z.1} :=
    (active_measurableSet L T k q).preimage measurable_fst
  have hb := measurableSet_le (timeMoment_measurable L μ T Λ k q m hm N)
    (((envelope_measurable L Q T A k q Cf ell A0 ν Cs).pow_const N).const_mul C)
  convert ha.compl.union hb using 1
  ext z
  simp only [mem_ofPred_eq,mem_compl_iff,mem_union,imp_iff_not_or]

end SHE.WeightedQuarterSpatialEvent
