module

public import SHE.PastMeanRMS
public import SHE.PastMeanDampedTime
public import SHE.RawTraceRMS

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.PastSignedEndpointTime
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope
  QuarterSpatialEvent PhysicalParentGeometry RawTraceTimeEnvelope
local instance pastSignedEndpointTime_period : Fact (0<2*π) := ⟨by positivity⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)

def freshCoefficient (P:CanonicalCovariance.ProfileParameters)(k:ℕ):ℝ:=
  ScalarMeanEnvelope.massCoefficient k 1*sqrt (4*UniformFutureProfileScores.constant (1+k)/(3*P.lower))

def goodCoefficient (P:CanonicalCovariance.ProfileParameters)(k:ℕ)(J ρ η:ℝ):ℝ:=
  sqrt (2*J*SignedKernelTruncation.nativeCostConstant ρ*logLossConstant η)*
    freshCoefficient P k*(2:ℝ)^(freshExponent ρ η)

def badCoefficient (P:CanonicalCovariance.ProfileParameters)(k:ℕ)(U C:ℝ):ℝ:=
  sqrt (8*U*C*NormalizedKernelSplit.heatMassConstant)*freshCoefficient P k*(2:ℝ)^(1/2:ℝ)

theorem freshCoefficient_nonneg (P:CanonicalCovariance.ProfileParameters)(k:ℕ):0≤freshCoefficient P k:=
  mul_nonneg (ScalarMeanEnvelope.massCoefficient_nonneg k zero_le_one) (sqrt_nonneg _)

theorem goodCoefficient_nonneg (P:CanonicalCovariance.ProfileParameters)(k:ℕ)(J ρ η:ℝ):
    0≤goodCoefficient P k J ρ η:=
  mul_nonneg (mul_nonneg (sqrt_nonneg _) (freshCoefficient_nonneg P k)) (rpow_nonneg (by norm_num) _)

theorem badCoefficient_nonneg (P:CanonicalCovariance.ProfileParameters)(k:ℕ)(U C:ℝ):
    0≤badCoefficient P k U C:=
  mul_nonneg (mul_nonneg (sqrt_nonneg _) (freshCoefficient_nonneg P k)) (rpow_nonneg (by norm_num) _)

private theorem sqrt_fresh_cancel {C ell g:ℝ}(hell:0<ell)(hg:0<g)(hC:0≤C):
    sqrt (2*C/(ell*(3*g/4)))*sqrt (g/2)=sqrt (4*C/(3*ell)):=by
  rw [←Real.sqrt_mul (by positivity : 0≤2*C/(ell*(3*g/4)))]
  congr 1
  field_simp

/-- The reserved right-heat square root cancels the fresh score square
root exactly, before either good or bad time singularity is integrated. -/
theorem amplitude_identity (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    (k:ℕ)(Λ q A0 ν:ℝ)(t:Fin k→ℝ)(ha:active L T k q t):
    let p:=anchor k t
    let g:=(carrier L k).terminal p-q
    PastMeanAmplitude.damped L P k Λ q A0 ν p*ScalarMeanEnvelope.massCoefficient k 1*
      sqrt (quarterTraceTime (R:=R) T k q t)=
      freshCoefficient P k*exp (-Λ*g/4)*
        (timeWeight L (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k p*
          PastWordTimeFields.total L P k p A0 ν) :=by
  intro p g
  have ht:(carrier L k).terminal p=fixedTerminal (R:=R) T k t:=terminal_separated L T hT k t _ _
  have hp:StrictHistory L k p ∧ q<(carrier L k).terminal p:=⟨ha.1,by simpa only [ht] using ha.2⟩
  have hg:0<g:=sub_pos.mpr hp.2
  have hrow:HistoryQuarterFields.rowTime L k q p=q+g/4:=by
    simp only [HistoryQuarterFields.rowTime,max_eq_left hg.le,g]
  have hfresh:(carrier L k).terminal p-HistoryQuarterFields.rowTime L k q p=3*g/4:=by
    rw [hrow];dsimp only [g];ring
  have hδ:quarterTraceTime (R:=R) T k q t=g/2:=by
    simp only [quarterTraceTime,quarterGap,←ht,max_eq_left hg.le,g]
  have hExp:exp (-Λ*(HistoryQuarterFields.rowTime L k q p-q))=exp (-Λ*g/4):=by
    rw [hrow];congr 1;ring
  have hW:0≤timeWeight L (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k p:=
    timeWeight_nonneg L (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) _
      (fun j=>(uniformConstant_pos 1 j).le) k p hp.1
  simp only [PastMeanAmplitude.damped,PastMeanAmplitude.value,max_eq_left hW,hfresh,hδ,hExp]
  calc
    _=(ScalarMeanEnvelope.massCoefficient k 1*
        (sqrt (2*UniformFutureProfileScores.constant (1+k)/(P.lower*(3*g/4)))*sqrt (g/2)))*
        exp (-Λ*g/4)*(timeWeight L (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k p*
          PastWordTimeFields.total L P k p A0 ν):=by ring
    _=_:=by rw [sqrt_fresh_cancel P.lower_pos hg (UniformFutureProfileScores.constant_pos (1+k)).le];rfl

/-- Literal endpoint good/bad RMS is bounded by the original positive
gap densities, retaining the true input negative energy. -/
theorem amplitude_bound (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    (k:ℕ)(Λ q A0 ν J ρ η lam ε U C tail E:ℝ)(hΛ:0≤Λ)(hρ:0≤ρ)(hη:0≤η)(hlam:0≤lam)
    (t:Fin k→ℝ)(ha:active L T k q t):
    let δ:=quarterTraceTime (R:=R) T k q t
    let w:=PastMeanEnvelope.width (R:=R) T k q t
    let D:=PastMeanAmplitude.damped L P k Λ q A0 ν (anchor k t)*ScalarMeanEnvelope.massCoefficient k 1*sqrt δ
    RawTraceTimeEnvelope.goodAmplitude J ρ η (lam^ε) D δ w*sqrt E+RawTraceTimeEnvelope.badAmplitude U C D δ lam tail≤
      goodCoefficient P k J ρ η*lam^ε*(T-q)^((ρ+η)/2)*sqrt E*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (freshDegree ρ η) A0 ν (anchor k t)+
      badCoefficient P k U C*lam^(-tail/2)*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (1/2:ℝ) A0 ν (anchor k t) :=by
  intro δ w D
  let p:=anchor k t
  let g:=(carrier L k).terminal p-q
  have ht:(carrier L k).terminal p=fixedTerminal (R:=R) T k t:=terminal_separated L T hT k t _ _
  have hp:StrictHistory L k p ∧ q<(carrier L k).terminal p:=⟨ha.1,by simpa only [ht] using ha.2⟩
  have hg:0<g:=sub_pos.mpr hp.2
  have hδ:δ=g/2:=by simp only [δ,quarterTraceTime,quarterGap,←ht,max_eq_left hg.le,g]
  have hD:D=freshCoefficient P k*exp (-Λ*g/4)*
      (timeWeight L (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k p*
        PastWordTimeFields.total L P k p A0 ν):=amplitude_identity L P T hT k Λ q A0 ν t ha
  have hw:0<w:=PastMeanEnvelope.width_pos L T hT k q t ha.2
  have hwle:w≤T-q:=by
    dsimp only [w,PastMeanEnvelope.width,quarterRowTime]
    linarith [quarterGap_nonneg (R:=R) T k q t]
  have hpow:w^((ρ+η)/2)≤(T-q)^((ρ+η)/2):=
    rpow_le_rpow hw.le hwle (by positivity)
  have he:exp (-Λ*g/4)≤1:=Real.exp_le_one_iff.mpr (by nlinarith)
  have hW:0≤timeWeight L (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k p:=
    timeWeight_nonneg L (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) _
      (fun j=>(uniformConstant_pos 1 j).le) k p hp.1
  have hTotal:=PastWordTimeFields.total_nonneg L P k p A0 ν
  have hgood:RawTraceTimeEnvelope.goodAmplitude J ρ η (lam^ε) D δ w*sqrt E=
      goodCoefficient P k J ρ η*lam^ε*w^((ρ+η)/2)*sqrt E*exp (-Λ*g/4)*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (freshDegree ρ η) A0 ν p:=by
    rw [hδ,goodAmplitude_half_gap J ρ η (lam^ε) D w hg,hD]
    have hex:freshDegree ρ η-1= -freshExponent ρ η:=by unfold freshDegree;ring
    simp only [RawTraceTimeEnvelope.goodAmplitude,goodCoefficient,PastMeanTimeFactors.totalIntegrand,if_pos hp,hex]
    ring
  have hbad:RawTraceTimeEnvelope.badAmplitude U C D δ lam tail=
      badCoefficient P k U C*lam^(-tail/2)*exp (-Λ*g/4)*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (1/2:ℝ) A0 ν p:=by
    rw [hδ,badAmplitude_half_gap U C D lam tail hg,hD]
    simp only [RawTraceTimeEnvelope.badAmplitude,badCoefficient,PastMeanTimeFactors.totalIntegrand,if_pos hp,
      show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num]
    ring
  have hIc:=PastMeanTimeFactors.totalIntegrand_nonneg L P
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
    (fun j=>(uniformConstant_pos 1 j).le) k q (freshDegree ρ η) A0 ν p
  have hIb:=PastMeanTimeFactors.totalIntegrand_nonneg L P
    (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
    (fun j=>(uniformConstant_pos 1 j).le) k q (1/2:ℝ) A0 ν p
  rw [hgood,hbad]
  apply add_le_add
  · have hc:0≤goodCoefficient P k J ρ η*lam^ε*sqrt E*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (freshDegree ρ η) A0 ν p:=by
      exact mul_nonneg (mul_nonneg (mul_nonneg (goodCoefficient_nonneg P k J ρ η)
        (rpow_nonneg hlam _)) (sqrt_nonneg _)) hIc
    have hh:=mul_le_mul_of_nonneg_left (mul_le_mul hpow he (exp_pos _).le
      (rpow_nonneg (hw.trans_le hwle).le _)) hc
    convert! hh using 1 <;> ring
  · have hc:0≤badCoefficient P k U C*lam^(-tail/2)*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (1/2:ℝ) A0 ν p:=
      mul_nonneg (mul_nonneg (badCoefficient_nonneg P k U C) (rpow_nonneg hlam _)) hIb
    have hh:=mul_le_mul_of_nonneg_left he hc
    convert! hh using 1 <;> ring

end SHE.PastSignedEndpointTime
