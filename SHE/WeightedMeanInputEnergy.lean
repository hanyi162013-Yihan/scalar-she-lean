module

public import SHE.CorrelatedKernelRelative
public import SHE.HeatedCurrentInput
public import SHE.WeightedMeanOperator
public import SHE.WeightedMeanInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NativeRandomKernel
open scoped ENNReal
local instance weightedMeanInputEnergy_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance weightedMeanInputEnergy_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance weightedMeanInputEnergy_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance weightedMeanInputEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance weightedMeanInputEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance weightedMeanInputEnergy_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance weightedMeanInputEnergy_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

/-- A genuine correlated quantitative mean-input bound for the actual
stop-weighted physical kernel. Its right heat is retained exactly, so
all pointwise input moments concern legitimate positive-age native
observations. The final small factor is the ORIGINAL global current
energy, with no independence assumption. -/
theorem weighted_mean_input_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : ∀ x,L.terminal x=T) (damping : ℝ) (hdamping : 0≤damping)
    (k : ℕ) (q r : ℝ) (t : Fin k→ℝ) (hqr : q<r)
    (hr : r<fixedTerminal (R:=R) T k t)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2))
    (V : Ω→RealL2) (hV : Measurable V) (hiV : Integrable (fun ω=>‖V ω‖^2) μ)
    {mass ρ w A χ CD CG : ℝ} (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (hw : 0<w) (hw1 : w≤1) (hA : 0≤A)
    (hχ0 : 0≤χ) (hχ1 : χ<1) (hCD : 0≤CD) (hCG : 0≤CG)
    (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (hiDh : ∀ y,Integrable (fun ω=>|functional (r-q) y (V ω)|^((4*(p:ℝ))*(1-χ))) μ)
    (hbDh : ∀ y,(∫ ω,|functional (r-q) y (V ω)|^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hMom : ∀ᵐ z : HeatCircle×HeatCircle ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      (∫ ω,‖weightedField L k damping q r m t (ω,z)‖^(4*p) ∂μ)≤
        CG*(A*‖ProfileVariance.heatPhysical (8*w) z.1 z.2‖)^(4*p)) :
    let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*A^2*((CD+CG)/2)^(1/(p:ℝ))
    Integrable (fun ω=>‖OneInputOperator.besselHalf mass ρ hmass hρ.le
      (integralOperator (weightedField L k damping q q m t) ω (embed (V ω)))‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (integralOperator (weightedField L k damping q q m t) ω (embed (V ω)))‖^2 ∂μ)≤
        C*(∫ ω,‖V ω‖^2 ∂μ)^χ := by
  intro C
  have hτ : 0<r-q := sub_pos.mpr hqr
  obtain ⟨B,hB,hbound⟩ := weightedSpatial_uniform_bound L (X:=Ω) T hT k hdamping q r t
  have hF := weightedField_measurable L k damping q r m hm t
  have hinput := HeatedCurrentInput.expected_field_mass μ hτ V hV hiV
  have hh := NativeRandomKernel.correlated_input_relative μ hF hB
    (fun ω y x=>hbound m ω y x) (HeatedCurrentInput.field (r-q) V)
    (HeatedCurrentInput.field_measurable (r-q) hV)
    (HeatedCurrentInput.value (r-q) V) (HeatedCurrentInput.value_ae hτ V)
    hinput.1 hinput.2.1 hmass hρ hρhalf hw hw1 hA (fun y=>y)
    hχ0 hχ1 hCD hCG p hp horder hiDh hbDh (fun y x=>by
      rw [←NativeHeatSpan.kernel_eq_physical (by positivity : 0<8*w)]
      exact NodeKernelLocal.kernel_norm_pos (NativeHeatSpan.clock_pos (by positivity : 0<8*w)) _) hMom
  have he (ω : Ω) : integralOperator (weightedField L k damping q q m t) ω (embed (V ω))=
      integralOperator (weightedField L k damping q r m t) ω (HeatedCurrentInput.value (r-q) V ω) := by
    rw [weighted_operator_split L T hT k hdamping q r m hm t hqr.le hr ω,
      ContinuousLinearMap.comp_apply]
    rw [←embed_heat hτ.le]
    rfl
  refine ⟨by simpa only [he] using hh.1,?_⟩
  have hC : 0≤C := by
    dsimp only [C]
    have htr := GaussianNegativePacket.traceConstant_pos
    have hg := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
    have hc := (NativeHeatSpan.clock_pos hw).le
    unfold GaussianNegativePacket.constant
    positivity
  have hlow := Real.rpow_le_rpow
    (integral_nonneg (fun y=>integral_nonneg (fun ω=>sq_nonneg (HeatedCurrentInput.field (r-q) V (ω,y)))))
    hinput.2.2 hχ0
  have hb := hh.2
  have hbound' : (∫ ω,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
      (integralOperator (weightedField L k damping q q m t) ω (embed (V ω)))‖^2 ∂μ)≤
        C*(∫ y,∫ ω,HeatedCurrentInput.field (r-q) V (ω,y)^2 ∂μ ∂haarAddCircle)^χ := by
    simpa only [he,C] using hb
  exact hbound'.trans (mul_le_mul_of_nonneg_left hlow hC)

end SHE.ActualMeanKernel
