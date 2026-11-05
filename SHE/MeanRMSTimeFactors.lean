module

public import SHE.InterpolatedMeanEnergy
public import SHE.QuarterRMSOldTime

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MeanRMSTimeFactors
open Set Filter MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel
  CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalAssignmentGapScale
  HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope QuarterSpatialEvent NormalizedKernelSplit
  QuarterRMSTimeFactors PhysicalParentGeometry
open scoped BigOperators
local instance meanRMSTimeFactors_nativePositive : Fact (0<2*π) := ⟨by positivity⟩

def prefactor (ρ C : ℝ) : ℝ :=
  Real.sqrt (GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock 1)^(ρ-1/2)*C)

def amplitude (ρ C D δ w : ℝ) : ℝ := prefactor ρ C*D*δ^(-(1/2:ℝ))*w^(ρ/2)

theorem amplitude_nonneg (ρ C : ℝ) {D δ w : ℝ} (hD : 0≤D) (hδ : 0≤δ) (hw : 0≤w) :
    0≤amplitude ρ C D δ w :=
  mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hD) (rpow_nonneg hδ _)) (rpow_nonneg hw _)

/-- The explicit quarter power in the true heat envelope cancels the
output packet's half-dimensional trace power, with the native clock
normalization retained. -/
theorem amplitude_sq {ρ C δ w : ℝ} (hρhalf : ρ<1/2) (hC : 0≤C)
    (hδ : 0<δ) (hw : 0<w) (D : ℝ) :
    amplitude ρ C D δ w^2=
      GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*
        (heatAmplitude D δ w)^2*C := by
  have hG : 0≤GaussianNegativePacket.constant ρ := by
    have htr := GaussianNegativePacket.traceConstant_pos
    have hg := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
    unfold GaussianNegativePacket.constant
    positivity
  have hc1 : 0≤NativeHeatSpan.clock 1 := (NativeHeatSpan.clock_pos (by norm_num)).le
  have hclock : NativeHeatSpan.clock w=NativeHeatSpan.clock 1*w := by unfold NativeHeatSpan.clock;ring
  have hp : (w^(ρ/2))^2=w^ρ := by
    rw [←Real.rpow_mul_natCast hw.le]
    congr 1
    ring
  have hq : (w^(1/4:ℝ))^2=w^(1/2:ℝ) := by
    rw [←Real.rpow_mul_natCast hw.le]
    norm_num
  have hcancel : w^(ρ-1/2)*w^(1/2:ℝ)=w^ρ := by
    rw [←Real.rpow_add hw]
    congr 1
    ring
  unfold amplitude prefactor heatAmplitude
  rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg (mul_nonneg hG (rpow_nonneg hc1 _)) hC),hp,
    hclock,Real.mul_rpow hc1 hw.le,mul_pow,mul_pow,hq]
  calc
    _=(GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock 1)^(ρ-1/2)*C)*D^2*
        (δ^(-(1/2:ℝ)))^2*(w^(ρ-1/2)*w^(1/2:ℝ)) := by rw [hcancel]
    _=_ := by ring

variable {R : ReferenceData} (L : CutoffWordLevel.Level R HeatCircle 1)

def timeFactor (ρ C : ℝ) (k : ℕ) (Cf ell w : ℝ) : ℝ :=
  prefactor ρ C*amplitudePrefactor k Cf ell*(2:ℝ)^(1/2:ℝ)*w^(ρ/2)

theorem timeFactor_nonneg (ρ C : ℝ) (k : ℕ) (Cf ell : ℝ) {w : ℝ} (hw : 0≤w) :
    0≤timeFactor ρ C k Cf ell w :=
  mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (amplitudePrefactor_nonneg _ _ _))
    (rpow_nonneg (by norm_num) _)) (rpow_nonneg hw _)

theorem active_identity (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν : ℝ) (Cs : ℕ→ℝ)
    (t : Fin k→ℝ) (ha : active L T k q t) (ρ C w : ℝ) :
    amplitude ρ C (QuarterSpatialEvent.amplitude L Q k q Cf ell A0 ν Cs t)
      (quarterTraceTime (R:=R) T k q t) w=
      timeFactor ρ C k Cf ell w*totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t) := by
  have hg : 0<fixedTerminal (R:=R) T k t-q := sub_pos.mpr ha.2
  have ht : (carrier L k).terminal (anchor k t)=fixedTerminal (R:=R) T k t :=
    terminal_separated L T hT k t _ _
  have hp : StrictHistory L k (anchor k t) ∧ q<(carrier L k).terminal (anchor k t) :=
    ⟨ha.1,by simpa only [ht] using ha.2⟩
  have hδ : quarterTraceTime (R:=R) T k q t=(fixedTerminal (R:=R) T k t-q)/2 := by
    rw [quarterTraceTime,(quarter_geometry T k q t ha.2).1]
  have hd : ((fixedTerminal (R:=R) T k t-q)/2)^(-(1/2:ℝ))=
      (2:ℝ)^(1/2:ℝ)*(fixedTerminal (R:=R) T k t-q)^(-(1/2:ℝ)) := by
    rw [Real.div_rpow hg.le (by norm_num : (0:ℝ)≤2),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ)≤2),neg_neg]
    ring
  rw [hδ]
  unfold amplitude
  rw [hd,amplitude_factor,totalIntegrand,ite_eq_left hp]
  simp only [timeFactor,ht,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num]
  ring

/-- All old times are integrated before squaring. The finite assignment
budget keeps every true root count and rough-block minimum gap. -/
theorem old_time_budget (Q : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {ell : ℝ} (hell : 0<ell)
    (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j) (k : ℕ)
    {q A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) (ρ C Cf w : ℝ) (hw : 0≤w) :
    Integrable (fun t=>timeFactor ρ C k Cf ell w*
      totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,timeFactor ρ C k Cf ell w*totalIntegrand L Q ell Cs k q (1/2:ℝ) A0 ν (anchor k t)
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
        timeFactor ρ C k Cf ell w*oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν := by
  have hh := total_old_time_budget L Q T hT hell Cs hCs k hqbase hqT hTH
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1) hA0 hν
  refine ⟨hh.1.const_mul _,?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hh.2 (timeFactor_nonneg ρ C k Cf ell hw)

end SHE.MeanRMSTimeFactors
