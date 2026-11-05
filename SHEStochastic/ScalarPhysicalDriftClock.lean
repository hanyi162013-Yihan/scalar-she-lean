module

public import SHEStochastic.ScalarStoppedDriftConvolution
public import SHEStochastic.ScalarStoppedDriftAlgebra
public import SHEStochastic.ScalarUnitTorusFourierClock
public import SHE.TimeDilationMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalDriftClock
open MeasureTheory Set SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos
local notation "clk" => clock r hr
local notation "tm" => PredictableL2.timeMeasure

variable {H : ℝ≥0} (b : ScalarLinearGrowthDriftField.Data H)

/-- The same Borel drift on the native clock, with the deterministic
time Jacobian and no Brownian square-root factor. -/
def native : ScalarLinearGrowthDriftField.Data (r*H) where
  value p := (r : ℝ)⁻¹*b.value ((clk).symm p.1,p.2)
  measurable := (b.measurable.comp (((clock_symm_continuous r hr).measurable.comp measurable_fst).prodMk
    measurable_snd)).const_mul _
  growth := r⁻¹*b.growth
  bound t ht x z := by
    have hT : (clk).symm t≤H := (clk).symm.monotone ht |>.trans_eq ((clk).symm_apply_apply H)
    have hInv : 0≤(r : ℝ)⁻¹ := inv_nonneg.mpr (show 0≤(r : ℝ) from (r).property)
    rw [abs_mul,abs_of_nonneg hInv,NNReal.coe_mul,NNReal.coe_inv,mul_assoc]
    exact mul_le_mul_of_nonneg_left (b.bound _ hT x z) hInv

theorem field (t : ℝ≥0) (u : RealL2) :
    ScalarLinearGrowthDriftField.field (native b) (clk t,u) =
      (r : ℝ)⁻¹ • ScalarLinearGrowthDriftField.field b (t,u) := by
  have ht : (clk).symm (min (clk t) (r*H)) = min t H := by
    change (clk).symm (min (clk t) (clk H)) = _
    rw [←Monotone.map_min (clk).monotone,(clk).symm_apply_apply]
  apply Lp.ext
  filter_upwards [ScalarLinearGrowthDriftField.field_ae (native b) (clk t,u),
    ScalarLinearGrowthDriftField.field_ae b (t,u),
    Lp.coeFn_smul ((r : ℝ)⁻¹) (ScalarLinearGrowthDriftField.field b (t,u))]
    with x hn hp hs
  rw [hn,hs,Pi.smul_apply,hp]
  change (r : ℝ)⁻¹*b.value ((clk).symm (min (clk t) (r*H)),(x,u x)) =
    (r : ℝ)⁻¹*b.value (min t H,(x,u x))
  rw [ht]

variable {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0→Ω→RealL2)
  (hc : ∀ ω,Continuous (fun t => U t ω))

local notation "W" => pullPath r hr U

include hc in
/-- Clock change preserves the strict norm exit, including a hit at the
observation time and the possible infinite exit. -/
theorem before_iff (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    ((clk t : ℝ≥0) : WithTop ℝ≥0)<ContinuousNormExit.exit U N ω ↔
      (t : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω := by
  rw [←not_le,←not_le,ContinuousNormExit.le_iff U hc,ContinuousNormExit.le_iff W
    (pullPath_continuous r hr U hc)]
  apply not_congr
  constructor
  · rintro ⟨s,hs,h⟩
    refine ⟨(clk).symm s,⟨zero_le,?_⟩,?_⟩
    · exact (clk).symm.monotone hs.2 |>.trans_eq ((clk).symm_apply_apply t)
    · change (N : ℝ)≤‖U (clk ((clk).symm s)) ω‖
      rwa [(clk).apply_symm_apply]
  · rintro ⟨s,hs,h⟩
    exact ⟨clk s,⟨zero_le,(clk).monotone hs.2⟩,h⟩

/-- The literal stopped Bochner convolution on the physical unit
circle. Its generator is ∂² and the time integral uses ordinary Lebesgue. -/
def physicalConvolution (N : ℕ) (ω : Ω) (t : ℝ≥0) : RealL2 :=
  ∫ s : ℝ≥0,RealHeat.realHeat ((t : ℝ)-(s : ℝ))
    (ScalarStoppedDriftConvolution.input b U (fun _ _ => 1) N ω s) ∂tm t

include hc in
theorem convolution (N : ℕ) (ω : Ω) (t : ℝ≥0) :
    ScalarStoppedDriftConvolution.convolution (native b) U (fun _ _ => 1) N ω (clk t) =
      physicalConvolution b W N ω t := by
  let f (s : ℝ≥0) := NativeHeatObservation.heat ((clk t : ℝ≥0)-(s : ℝ))
    (ScalarStoppedDriftConvolution.input (native b) U (fun _ _ => 1) N ω s)
  let q (s : ℝ≥0) := RealHeat.realHeat ((t : ℝ)-(s : ℝ))
    (ScalarStoppedDriftConvolution.input b W (fun _ _ => 1) N ω s)
  have hf : Integrable f (tm (clk t)) :=
    ScalarStoppedDriftAlgebra.integrable (native b) U hc N ω (clk t) (fun _ _ => 1)
      measurable_const (fun _ => by norm_num)
  have he (s : ℝ≥0) : f (clk s) = (r : ℝ)⁻¹ • q s := by
    have hheat : ((clk t : ℝ≥0)-(clk s : ℝ≥0))/NativeHeatObservation.timeScale =
        (t : ℝ)-(s : ℝ) := by
      change ((r : ℝ)*(t : ℝ)-(r : ℝ)*(s : ℝ))/(r : ℝ)=_
      field_simp [(show (r : ℝ)≠0 from ne_of_gt hr)]
    have hb : (clk s : WithTop ℝ≥0)<ContinuousNormExit.exit U N ω ↔
        (s : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω := before_iff U hc N s ω
    dsimp only [f,q,NativeHeatObservation.heat,ScalarStoppedDriftConvolution.input]
    rw [hheat]
    by_cases hs : (s : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω
    · rw [ite_eq_left hs,ite_eq_left (hb.mpr hs),one_smul,one_smul,field,map_smul]
      rfl
    · rw [ite_eq_right hs,ite_eq_right (mt hb.mp hs),map_zero,smul_zero]
  have hp : MeasurePreserving (clk) (ENNReal.ofReal (r : ℝ) • tm t) (tm (clk t)) :=
    timeMeasure_clock_preserving r hr t
  change (∫ s,f s ∂tm (clk t))=∫ s,q s ∂tm t
  calc
    _ = ∫ s,f (clk s) ∂(ENNReal.ofReal (r : ℝ) • tm t) := by
      have hm : AEStronglyMeasurable f ((ENNReal.ofReal (r : ℝ) • tm t).map (clk)) := by
        rw [hp.map_eq]
        exact hf.aestronglyMeasurable
      rw [←hp.map_eq,integral_map hp.measurable.aemeasurable hm]
    _ = _ := by
      simp_rw [he]
      have hrR : (ENNReal.ofReal (r : ℝ)).toReal=(r : ℝ) :=
        ENNReal.toReal_ofReal (show 0≤(r : ℝ) from (r).property)
      rw [integral_smul_measure,hrR,integral_smul,smul_smul,
        mul_inv_cancel₀ (show (r : ℝ)≠0 from ne_of_gt hr),one_smul]

end SHEStochastic.ScalarPhysicalDriftClock
