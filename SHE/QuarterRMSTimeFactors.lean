module

public import SHE.RawTraceRMS
public import SHE.QuarterSpatialEvent
public import SHE.PhysicalAssignedTimeTotal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace SHE.QuarterRMSTimeFactors
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope
  QuarterSpatialEvent NormalizedKernelSplit RawTraceTimeEnvelope PhysicalAssignmentGapScale
  GaussianAssignmentBlocks AllocatedAssignmentKernel CoveredHistoryGeometry PhysicalParentGeometry
open scoped BigOperators
local instance quarterRMSTimeFactors_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
variable {R : ReferenceData} (L : CutoffWordLevel.Level R HeatCircle 1)

def amplitudePrefactor (k : ℕ) (Cf ell : ℝ) : ℝ := quarterAmplitude k Cf ell 1 1

theorem amplitudePrefactor_nonneg (k : ℕ) (Cf ell : ℝ) : 0≤amplitudePrefactor k Cf ell :=
  quarterAmplitude_nonneg k zero_le_one zero_le_one

theorem quarterAmplitude_factor (k : ℕ) (Cf ell D W : ℝ) :
    quarterAmplitude k Cf ell D W=amplitudePrefactor k Cf ell*D*W := by
  unfold amplitudePrefactor quarterAmplitude ScalarMeanEnvelope.massCoefficient
  ring

theorem amplitude_factor (Q : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (q Cf ell A0 ν : ℝ) (Cs : ℕ→ℝ) (t : Fin k→ℝ) :
    amplitude L Q k q Cf ell A0 ν Cs t=
      amplitudePrefactor k Cf ell*timeWeight L ell Cs k (anchor k t)*
        SharpWordTimeScale.total L Q k (anchor k t) q A0 ν := by
  unfold amplitude
  rw [quarterAmplitude_factor]
  ring

def goodTimeFactor (J ρ η R : ℝ) (k : ℕ) (Cf ell w : ℝ) : ℝ :=
  goodAmplitude J ρ η R (amplitudePrefactor k Cf ell) 1 w*2^(freshExponent ρ η)

def badTimeFactor (U C : ℝ) (k : ℕ) (Cf ell lam tail : ℝ) : ℝ :=
  RawTraceTimeEnvelope.badAmplitude U C (amplitudePrefactor k Cf ell) 1 lam tail*2^(1/2:ℝ)

theorem goodTimeFactor_nonneg (J ρ η : ℝ) {R w : ℝ} (hR : 0≤R) (hw : 0≤w)
    (k : ℕ) (Cf ell : ℝ) : 0≤goodTimeFactor J ρ η R k Cf ell w :=
  mul_nonneg (goodAmplitude_nonneg J ρ η hR (amplitudePrefactor_nonneg k Cf ell) zero_le_one hw)
    (Real.rpow_nonneg (by norm_num) _)

theorem badTimeFactor_nonneg (U C : ℝ) {lam : ℝ} (hlam : 0≤lam)
    (k : ℕ) (Cf ell tail : ℝ) : 0≤badTimeFactor U C k Cf ell lam tail :=
  mul_nonneg (badAmplitude_nonneg U C tail (amplitudePrefactor_nonneg k Cf ell) zero_le_one hlam)
    (Real.rpow_nonneg (by norm_num) _)

/-- Exact conversion of the good RMS density into the genuine physical
old-time integrand, with freshDegree and every assignment minimum gap. -/
theorem good_active_identity (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν : ℝ) (Cs : ℕ→ℝ)
    (t : Fin k→ℝ) (ha : active L T k q t) (J ρ η cutoff w : ℝ) :
    goodAmplitude J ρ η cutoff (amplitude L Q k q Cf ell A0 ν Cs t)
      (quarterTraceTime (R:=R) T k q t) w=
      goodTimeFactor J ρ η cutoff k Cf ell w*
        totalIntegrand L Q ell Cs k q (freshDegree ρ η) A0 ν (anchor k t) := by
  have hg : 0<fixedTerminal (R:=R) T k t-q := sub_pos.mpr ha.2
  have ht : (carrier L k).terminal (anchor k t)=fixedTerminal (R:=R) T k t :=
    terminal_separated L T hT k t _ _
  have hp : StrictHistory L k (anchor k t) ∧ q<(carrier L k).terminal (anchor k t) :=
    ⟨ha.1,by simpa only [ht] using ha.2⟩
  have hδ : quarterTraceTime (R:=R) T k q t=(fixedTerminal (R:=R) T k t-q)/2 := by
    rw [quarterTraceTime,(quarter_geometry T k q t ha.2).1]
  rw [hδ,goodAmplitude_half_gap J ρ η cutoff _ w hg,totalIntegrand,ite_eq_left hp]
  simp only [goodTimeFactor,goodAmplitude,one_rpow,amplitude_factor,ht,
    show freshDegree ρ η-1= -freshExponent ρ η by unfold freshDegree;ring]
  ring

/-- The bad-tail RMS density has fresh degree 1/2 and keeps the SAME
sharp old-time assignment factor; no old-time supremum is taken. -/
theorem bad_active_identity (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν : ℝ) (Cs : ℕ→ℝ)
    (t : Fin k→ℝ) (ha : active L T k q t) (U C lam tail : ℝ) :
    RawTraceTimeEnvelope.badAmplitude U C (amplitude L Q k q Cf ell A0 ν Cs t)
      (quarterTraceTime (R:=R) T k q t) lam tail=
      badTimeFactor U C k Cf ell lam tail*
        totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t) := by
  have hg : 0<fixedTerminal (R:=R) T k t-q := sub_pos.mpr ha.2
  have ht : (carrier L k).terminal (anchor k t)=fixedTerminal (R:=R) T k t :=
    terminal_separated L T hT k t _ _
  have hp : StrictHistory L k (anchor k t) ∧ q<(carrier L k).terminal (anchor k t) :=
    ⟨ha.1,by simpa only [ht] using ha.2⟩
  have hδ : quarterTraceTime (R:=R) T k q t=(fixedTerminal (R:=R) T k t-q)/2 := by
    rw [quarterTraceTime,(quarter_geometry T k q t ha.2).1]
  rw [hδ,badAmplitude_half_gap U C _ lam tail hg,totalIntegrand,ite_eq_left hp]
  simp only [badTimeFactor,RawTraceTimeEnvelope.badAmplitude,one_rpow,amplitude_factor,ht,
    show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num]
  ring

end SHE.QuarterRMSTimeFactors
