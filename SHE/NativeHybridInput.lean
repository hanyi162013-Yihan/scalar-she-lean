module

public import SHE.NativeStoppedBracket
public import SHE.PredictableBracketAdd
public import SHE.NativeTwoChannelMoments
public import SHE.PredictableDamping

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeHybridInput
open Set MeasureTheory ProbabilityTheory Real PredictableL2 StoppedFourier FiniteHaar
  OrthogonalItoChannels PredictableItoRotation ProfileVariance
open scoped NNReal ENNReal
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def rightLift (v : Process (E := RealHaarInput) 𝓕 μ H) : Process (E := Both RealHaarInput) 𝓕 μ H :=
  processIsometry 𝓕 μ H (fun _ => right (C := RealHaarInput)) (right_measurable 𝓕) v

omit [IsProbabilityMeasure μ] in
theorem weighted_const_eq {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [MeasurableSpace C] [BorelSpace C]
    [SecondCountableTopology C]
    (θ : ℝ) (hθ : |θ| ≤ 1) (v : Process (E := C) 𝓕 μ H) :
    PredictableContraction.weighted 𝓕 μ H (fun _ => θ) stronglyMeasurable_const (fun _ => hθ) v = θ • v := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [PredictableContraction.weighted_ae 𝓕 μ H (fun _ => θ) stronglyMeasurable_const
    (fun _ => hθ) v,ae_eq_of_ae_eq_trim (Lp.coeFn_smul θ v)] with p hp hq
  rw [hp,hq]
  rfl

variable {ell₀ M₀ ell M : ℝ} (hell₀ : 0 < ell₀) (hM₀ : 0 ≤ M₀)
variable (f₀ : ℝ≥0 × Ω → EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell : 0 < ell) (hM : 0 ≤ M)
variable (fU fV : ℝ≥0 × Ω → EllipticField ell M)
variable (hfU : StronglyMeasurable[𝓕.predictable] fU) (hfV : StronglyMeasurable[𝓕.predictable] fV)
variable (q : ℝ≥0) {T : ℝ} (hT : (q : ℝ) < T) (x : HeatCircle)
variable {Λ θ : ℝ} (hΛ : 0 ≤ Λ) (hθ : |θ| ≤ 1)

def current : Process (E := Both RealHaarInput) 𝓕 μ H :=
  TwoChannelItoRows.block 𝓕 μ H
    (NativeObservationProcess.process 𝓕 μ H hell₀ hM₀ f₀ hf₀ hT x)
    (NativeObservationProcess.process 𝓕 μ H hell hM fU hfU hT x)

def dampedDifference : Process (E := RealHaarInput) 𝓕 μ H :=
  PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ q)
    (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q)
    (NativeObservationProcess.process 𝓕 μ H hell hM fV hfV hT x -
      NativeObservationProcess.process 𝓕 μ H hell hM fU hfU hT x)

/-- Literal centered hybrid current input in the same original full-H
two-channel integral. The additive channel is shared and cancels from the
controlled difference; exponential damping is retained only on that difference. -/
def input : Process (E := Both RealHaarInput) 𝓕 μ H :=
  current 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU hfU q hT x +
    rightLift 𝓕 μ H (PredictableContraction.weighted 𝓕 μ H (fun _ => θ)
      stronglyMeasurable_const (fun _ => hθ)
      (dampedDifference 𝓕 μ H hell hM fU fV hfU hfV q hT x hΛ))

theorem bracket_bound (hqH : q ≤ H) (hq1 : (q : ℝ) ≤ 1) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ (s,ω)‖^2) ∂timeMeasure H) ≤
        ENNReal.ofReal (upperConstant*(2*M₀+10*M)*(q : ℝ)^(1/2 : ℝ)) := by
  let K₀ := upperConstant*M₀*(q : ℝ)^(1/2 : ℝ)
  let K := upperConstant*M*(q : ℝ)^(1/2 : ℝ)
  have hK₀ : 0 ≤ K₀ := mul_nonneg (mul_nonneg upperConstant_pos.le hM₀) (rpow_nonneg q.2 _)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg upperConstant_pos.le hM) (rpow_nonneg q.2 _)
  let v₀ := NativeObservationProcess.process 𝓕 μ H hell₀ hM₀ f₀ hf₀ hT x
  let vU := NativeObservationProcess.process 𝓕 μ H hell hM fU hfU hT x
  let vV := NativeObservationProcess.process 𝓕 μ H hell hM fV hfV hT x
  have h₀ := NativeStoppedBracket.bracket_bound 𝓕 μ H q hqH hq1 hell₀ hM₀ f₀ hf₀ hT x
  have hU := NativeStoppedBracket.bracket_bound 𝓕 μ H q hqH hq1 hell hM fU hfU hT x
  have hV := NativeStoppedBracket.bracket_bound 𝓕 μ H q hqH hq1 hell hM fV hfV hT x
  have hcur := TwoChannelMomentBracket.bracket_block_bound 𝓕 μ H v₀ vU hK₀ hK h₀ hU
  have hsub := PredictableBracketDifference.bracket_sub_bound 𝓕 μ H vV vU hK hV hU
  let dv := dampedDifference 𝓕 μ H hell hM fU fV hfU hfV q hT x hΛ
  have hdamp := PredictableContraction.bracket_le 𝓕 μ H (PredictableDamping.weight Λ q)
    (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q) (vV-vU)
  let tv := PredictableContraction.weighted 𝓕 μ H (fun _ => θ) stronglyMeasurable_const (fun _ => hθ) dv
  have hθb := PredictableContraction.bracket_le 𝓕 μ H (fun _ => θ) stronglyMeasurable_const (fun _ => hθ) dv
  have hright := PredictableItoRotation.bracket_ae 𝓕 μ H
    (fun _ => right (C := RealHaarInput)) (right_measurable 𝓕) tv
  have hrightBound : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖rightLift 𝓕 μ H tv (s,ω)‖^2) ∂timeMeasure H) ≤ ENNReal.ofReal (4*K) := by
    filter_upwards [hsub,hdamp,hθb,hright] with ω hs hd ht hr
    change (∫⁻ s, ENNReal.ofReal (‖rightLift 𝓕 μ H tv (s,ω)‖^2) ∂timeMeasure H) = _ at hr
    rw [hr]
    exact ht.trans (hd.trans hs)
  have hadd := PredictableBracketAdd.bracket_add_bound 𝓕 μ H
    (current 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU hfU q hT x) (rightLift 𝓕 μ H tv)
    (add_nonneg hK₀ hK) (mul_nonneg (by norm_num) hK) hcur hrightBound
  filter_upwards [hadd] with ω hω
  exact hω.trans_eq (congrArg ENNReal.ofReal (by dsimp [K₀,K];ring))

theorem integral_eq (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H) :
    J.integral (input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ) =
      J.integral (current 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU hfU q hT x) +
        θ • (rightIntegral 𝓕 μ H J).integral
          (dampedDifference 𝓕 μ H hell hM fU fV hfU hfV q hT x hΛ) := by
  rw [input,weighted_const_eq]
  unfold rightLift
  rw [map_smul,map_add,map_smul]
  rfl

end SHE.NativeHybridInput
