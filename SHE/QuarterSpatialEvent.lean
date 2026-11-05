module

public import SHE.MixedJointSpatialMoments
public import SHE.SharpTimeSections
public import SHE.FixedHistoryDomain
public import SHE.QuarterHeatNormalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.QuarterSpatialEvent
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure ActualMeanKernel
  ScalarMeanEnvelope NormalizedKernelSplit
local instance quarterSpatialEvent_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

def anchor (k : ℕ) (t : Fin k → ℝ) : History HeatCircle k :=
  separated k ((0:HeatCircle),t,fun _ => (0:HeatCircle))

theorem anchor_measurable (k : ℕ) : Measurable (anchor k) :=
  (separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))

def active (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k → ℝ) : Prop :=
  StrictHistory L k (anchor k t) ∧ q < fixedTerminal (R:=R) T k t

theorem active_measurableSet (T : ℝ) (k : ℕ) (q : ℝ) :
    MeasurableSet {t | active L T k q t} :=
  ((strictHistory_measurableSet L k).preimage (anchor_measurable k)).inter
    (measurableSet_lt measurable_const (fixedTerminal_continuous (R:=R) T k).measurable)

def timeMoment (μ : Measure Ω) (T : ℝ) (k : ℕ) (q : ℝ)
    (m : Ω → History HeatCircle k → WordRecursion.State (1+k)) (N : ℕ)
    (z : (Fin k → ℝ) × Space) : ℝ :=
  ∫ ω,‖rowSpatial L k q (quarterRowTime (R:=R) T k q z.1) m z.1 ω z.2.1 z.2.2‖^N ∂μ

/-- The actual post-old-space moment is jointly Borel in ALL remaining
old times and physical input/output coordinates. This event, rather than
a family of chosen time sections, is used in the next Fubini step. -/
theorem timeMoment_measurable (μ : Measure Ω) [SFinite μ] (T : ℝ) (k : ℕ) (q : ℝ)
    (m : Ω → History HeatCircle k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2)) (N : ℕ) :
    Measurable (timeMoment L μ T k q m N) := by
  let M : (Ω × (Fin k → ℝ)) → History HeatCircle k → WordRecursion.State (1+k) :=
    fun z p => m z.1 p
  have hM : Measurable (fun z : (Ω × (Fin k → ℝ)) × History HeatCircle k => M z.1 z.2) :=
    hm.comp (measurable_fst.fst.prodMk measurable_snd)
  have hr : Measurable (fun z : Ω × (Fin k → ℝ) => quarterRowTime (R:=R) T k q z.2) :=
    quarterRowTime_measurable T k measurable_const measurable_snd
  have hh := rowSpatial_variable_measurable L k (fun _ : Ω × (Fin k → ℝ) => q)
    (fun z => quarterRowTime (R:=R) T k q z.2) measurable_const hr M hM Prod.snd measurable_snd
  have hp : Measurable (fun z : ((Fin k → ℝ) × Space) × Ω => ((z.2,z.1.1),z.1.2)) :=
    (measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd
  have hnorm : Measurable (fun z : ((Fin k → ℝ) × Space) × Ω =>
      ‖rowSpatial L k q (quarterRowTime (R:=R) T k q z.1.1) m z.1.1 z.2 z.1.2.1 z.1.2.2‖^N) :=
    (hh.comp hp).norm.pow_const N
  exact (hnorm.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable

def amplitude (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν : ℝ)
    (Cs : ℕ → ℝ) (t : Fin k → ℝ) : ℝ :=
  quarterAmplitude k Cf ell (SharpWordTimeScale.total L Q k (anchor k t) q A0 ν)
    (timeWeight L ell Cs k (anchor k t))

theorem amplitude_measurable (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν : ℝ)
    (Cs : ℕ → ℝ) : Measurable (amplitude L Q k q Cf ell A0 ν Cs) := by
  have hD := (SharpWordTimeScale.total_measurable L Q k q A0 ν).comp (anchor_measurable k)
  have hW := (FixedHistoryTimeFactors.timeWeight_measurable L ell Cs k).comp (anchor_measurable k)
  unfold amplitude quarterAmplitude ScalarMeanEnvelope.massCoefficient
  exact ((measurable_const.mul measurable_const).mul hD).mul
    (measurable_const.mul (((hW.mul_const _).mul_const _).mul_const _))

theorem envelope_measurable (Q : CanonicalCovariance.ProfileParameters) (T A : ℝ)
    (k : ℕ) (q Cf ell A0 ν : ℝ) (Cs : ℕ → ℝ) :
    Measurable (fun z : (Fin k → ℝ) × Space =>
      heatEnvelope (amplitude L Q k q Cf ell A0 ν Cs z.1)
        (quarterTraceTime (R:=R) T k q z.1) (A-q) z.2) := by
  have hD : Measurable (fun z : (Fin k → ℝ) × Space => amplitude L Q k q Cf ell A0 ν Cs z.1) :=
    (amplitude_measurable L Q k q Cf ell A0 ν Cs).comp measurable_fst
  have hδ : Measurable (fun z : (Fin k → ℝ) × Space => quarterTraceTime (R:=R) T k q z.1) :=
    quarterTraceTime_measurable T k measurable_const measurable_fst
  have hk : Measurable (fun z : (Fin k → ℝ) × Space =>
      ‖ProfileVariance.heatPhysical (8*(A-q)) z.2.1 z.2.2‖) :=
    (ProfileVariance.heatPhysical_joint_measurable.comp
      ((measurable_const.prodMk measurable_snd.fst).prodMk measurable_snd.snd)).norm
  exact ((hD.mul (hδ.pow_const (-(1/2:ℝ)))).mul_const _).mul hk

theorem moment_event_measurableSet (μ : Measure Ω) [SFinite μ]
    (T A : ℝ) (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν C : ℝ)
    (Cs : ℕ → ℝ) (m : Ω → History HeatCircle k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2)) (N : ℕ) :
    MeasurableSet {z : (Fin k → ℝ) × Space | active L T k q z.1 →
      timeMoment L μ T k q m N z ≤
        C*(heatEnvelope (amplitude L Q k q Cf ell A0 ν Cs z.1)
          (quarterTraceTime (R:=R) T k q z.1) (A-q) z.2)^N} := by
  have ha : MeasurableSet {z : (Fin k → ℝ) × Space | active L T k q z.1} :=
    (active_measurableSet L T k q).preimage measurable_fst
  have hb := measurableSet_le (timeMoment_measurable L μ T k q m hm N)
    (((envelope_measurable L Q T A k q Cf ell A0 ν Cs).pow_const N).const_mul C)
  convert ha.compl.union hb using 1
  ext z
  simp only [mem_ofPred_eq,mem_compl_iff,mem_union,imp_iff_not_or]

end SHE.QuarterSpatialEvent
