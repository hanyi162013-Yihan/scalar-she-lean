module

public import SHE.PastMeanTimeIntegral
public import SHE.PastMeanEnvelope
public import SHE.MeanRMSTimeFactors

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanRMS
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope
  QuarterSpatialEvent PhysicalParentGeometry
local instance pastMeanRMS_period : Fact (0<2*π) := ⟨by positivity⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)

def coefficient (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (ρ C : ℝ) : ℝ :=
  MeanRMSTimeFactors.prefactor ρ C*ScalarMeanEnvelope.massCoefficient k 1*
    sqrt (8*UniformFutureProfileScores.constant (1+k)/(3*P.lower))

theorem coefficient_nonneg (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (ρ C : ℝ) :
    0≤coefficient P k ρ C :=
  mul_nonneg (mul_nonneg (sqrt_nonneg _) (ScalarMeanEnvelope.massCoefficient_nonneg k zero_le_one)) (sqrt_nonneg _)

theorem sqrt_fresh {C ell g : ℝ} (hell : 0<ell) (hg : 0<g) (hC : 0≤C) :
    sqrt (2*C/(ell*(3*g/4)))=sqrt (8*C/(3*ell))*g^(-(1/2:ℝ)) := by
  have he : 2*C/(ell*(3*g/4))=(8*C/(3*ell))/g := by
    field_simp
    <;> ring
  rw [he,Real.sqrt_div,show sqrt g=g^(1/2:ℝ) from sqrt_eq_rpow g,div_eq_mul_inv,←rpow_neg hg.le] <;> positivity

/-- The exact native quarter-age trace converts to the genuine relative
old-time RMS density. The native 4π² normalization is retained. -/
theorem active_identity (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (Λ q A0 ν ρ C : ℝ) (hρhalf : ρ<1/2) (hC : 0≤C)
    (t : Fin k→ℝ) (ha : active L T k q t) :
    let w:=PastMeanEnvelope.width (R:=R) T k q t
    let a:=PastMeanEnvelope.amplitude L P T k Λ q A0 ν t
    GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*a^2*C=
      (coefficient P k ρ C*w^(ρ/2)*
        exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (1/2:ℝ) A0 ν (anchor k t))^2 := by
  intro w a
  let p:=anchor k t
  let g:=(carrier L k).terminal p-q
  have ht : (carrier L k).terminal p=fixedTerminal (R:=R) T k t:=terminal_separated L T hT k t _ _
  have hp : StrictHistory L k p ∧ q<(carrier L k).terminal p:=⟨ha.1,by simpa only [ht] using ha.2⟩
  have hg : 0<g:=sub_pos.mpr hp.2
  have hw : 0<w:=PastMeanEnvelope.width_pos L T hT k q t ha.2
  have hrow : HistoryQuarterFields.rowTime L k q p=q+g/4 := by
    simp only [HistoryQuarterFields.rowTime,max_eq_left hg.le,g]
  have hfresh : (carrier L k).terminal p-HistoryQuarterFields.rowTime L k q p=3*g/4 := by
    rw [hrow]
    dsimp only [g]
    ring
  have hExp : exp (-Λ*(HistoryQuarterFields.rowTime L k q p-q))=
      exp (-Λ*((carrier L k).terminal p-q)/4) := by rw [hrow];congr 1;ring
  have hW : 0≤timeWeight L (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) k p:=
    timeWeight_nonneg L (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k p hp.1
  let D:=PastMeanAmplitude.damped L P k Λ q A0 ν p*ScalarMeanEnvelope.massCoefficient k 1
  have hh:=MeanRMSTimeFactors.amplitude_sq (ρ:=ρ) (C:=C) (δ:=1) hρhalf hC (by norm_num) hw D
  have hid : MeanRMSTimeFactors.amplitude ρ C D 1 w=
      coefficient P k ρ C*w^(ρ/2)*exp (-Λ*((carrier L k).terminal p-q)/4)*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (1/2:ℝ) A0 ν p := by
    unfold MeanRMSTimeFactors.amplitude
    simp only [one_rpow,mul_one,D,PastMeanAmplitude.damped,PastMeanAmplitude.value,max_eq_left hW,
      hfresh,sqrt_fresh P.lower_pos hg (UniformFutureProfileScores.constant_pos (1+k)).le,hExp,PastMeanTimeFactors.totalIntegrand,if_pos hp,
      show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num]
    unfold coefficient
    ring
  rw [hid] at hh
  simpa only [NormalizedKernelSplit.heatAmplitude,one_rpow,mul_one,D,mul_pow,PastMeanEnvelope.amplitude,p,w,a,mul_assoc] using hh.symm

theorem cap_bound (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (Λ q A0 ν ρ C : ℝ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hC : 0≤C)
    (t : Fin k→ℝ) (ha : active L T k q t) :
    let w:=PastMeanEnvelope.width (R:=R) T k q t
    let a:=PastMeanEnvelope.amplitude L P T k Λ q A0 ν t
    GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*a^2*C≤
      (coefficient P k ρ C*(T-q)^(ρ/2)*
        exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
        PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
          k q (1/2:ℝ) A0 ν (anchor k t))^2 := by
  intro w a
  rw [active_identity L P T hT k Λ q A0 ν ρ C hρhalf hC t ha]
  have hw:=PastMeanEnvelope.width_pos L T hT k q t ha.2
  have hwle : w≤T-q := by
    dsimp only [w,PastMeanEnvelope.width,quarterRowTime]
    linarith [quarterGap_nonneg (R:=R) T k q t]
  have hpow : w^(ρ/2)≤(T-q)^(ρ/2):=rpow_le_rpow hw.le hwle (div_nonneg hρ (by norm_num))
  have hIt : 0≤PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
      k q (1/2:ℝ) A0 ν (anchor k t) := by
    unfold PastMeanTimeFactors.totalIntegrand
    split_ifs with hp
    · exact mul_nonneg (rpow_nonneg (sub_pos.mpr hp.2).le _) (mul_nonneg
        (timeWeight_nonneg L (mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos) (uniformConstant 1)
          (fun j=>(uniformConstant_pos 1 j).le) k _ hp.1)
        (PastWordTimeFields.total_nonneg L P k _ A0 ν))
    · exact le_rfl
  apply pow_le_pow_left₀
  · exact mul_nonneg (mul_nonneg (mul_nonneg (coefficient_nonneg P k ρ C) (rpow_nonneg hw.le _)) (exp_pos _).le) hIt
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (coefficient_nonneg P k ρ C)) (exp_pos _).le) hIt

end SHE.PastMeanRMS
