module

public import SHE.ShiftedScoreArrays
public import SHE.ActualBaselineMarkFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.ShiftedPhysicalMarks
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ShiftedPhysicalArrays ShiftedScoreArrays PhysicalChainArrays PhysicalScoreChain
  StoppedGaussianFeatures ObservationTimeShift GaussianConvolution
open scoped BigOperators
local instance shiftedPhysicalMarks_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R Q : ReferenceData} {n : ℕ}
variable (L : Level R X n) (K : Level Q X n) (v : ℝ)
variable (hb : Q.base=R.base+v) (hT : ∀ x,K.terminal x=L.terminal x+v)
variable (hZ : ∀ x,K.observations.observations x=observations v (L.observations.observations x))
variable (hc : Q.reference=profile v R.reference)
variable (hV : Q.totalVariance=R.totalVariance) (hF : ∀ x,K.test x=L.test x)
include hb hT hZ hc hV hF

/-- Literal continuum covariance marks transport their signed profile
direction and their entire original stopped row, together with the
same fixed-old score law. -/
theorem covariance_point_shift (hR : 0≤R.base) (hv : 0≤v) (c e : Domain→ℝ)
    (k : ℕ) (p : History X k) (q : ℝ) (m : WordRecursion.State (n+k)) :
    ActualCovarianceMarkFields.point K (profile v c) (profile v e) k (q+v) m (shift v k p)=
      ActualCovarianceMarkFields.point L c e k q m p := by
  classical
  unfold ActualCovarianceMarkFields.point
  rw [terminal_shift L K v hb hT k p]
  simp only [add_lt_add_iff_right]
  split_ifs
  · rw [fullResidualCovariance_shift L K v hb hT hZ hc hR hv c k p q,
      oldAverage_shift L K v hb hT hZ hc hV hF hR hv c k p,
      stops_shift L K v hb hT hZ k p,targets_shift L K v hb hT hZ k p,centers_shift L K v hb hT hZ k p]
    unfold FiniteWordScores.covarianceMark
    congr 1
    rw [←integral_history_translation v q]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [profile_translation,stoppedRow_translation]
  · rfl

/-- Every erased-baseline test, with its original sign and exact
normalization, obeys the same physical clock translation. -/
theorem baseline_point_shift (hR : 0≤R.base) (hv : 0≤v) (c : Domain→ℝ)
    (k : ℕ) (p : History X k) (q : ℝ) (db : Fin k→ℝ) (m : WordRecursion.State (n+k)) :
    ActualBaselineMarkFields.point K (profile v c) k (q+v) db m (shift v k p)=
      ActualBaselineMarkFields.point L c k q db m p := by
  classical
  unfold ActualBaselineMarkFields.point
  rw [terminal_shift L K v hb hT k p]
  simp only [add_lt_add_iff_right]
  split_ifs
  · unfold baselineMark
    simp_rw [omittedAverage_shift L K v hb hT hZ hc hV hF hR hv c k p q]
  · rfl

end SHE.ShiftedPhysicalMarks
