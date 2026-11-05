module

public import SHEStochastic.ScalarStoppedDriftFourier
public import SHEStochastic.ScalarDriftNativeDirection
public import SHEStochastic.NativeCrossEnergy
public import SHE.TimeMeasureRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedHeatCross
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "tm" => PredictableL2.timeMeasure

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (N : ℕ) (t : ℝ≥0) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "row" => ScalarStoppedHeatFourierInput.row W hg hβ hβ₁ N t ψ n
local notation "v" => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁ N t ψ n

/-- The raw native terminal integral uses the same predictable heat row. -/
theorem raw_row : FiniteCylindricalIto.processTransport v =ᵐ[νin] row :=
  NativeRowRepresentatives.transport_ae v row
    (ScalarStoppedHeatFourierInput.predictable F W hW hc hg hβ hβ₁ N t ψ n)
    (ScalarStoppedHeatFourierInput.input_ae F μ H W hW hc hg hβ hβ₁ N t ψ n)

variable (b : ScalarLinearGrowthDriftField.Data H)
  (c : ℝ≥0) (hc₀ : 0<c) (hg₀ : ∀ z,(c : ℝ)≤|g z|)
  (a : ℝ≥0 → Ω → ℝ)

local notation "bθ" => ScalarLinearGrowthDriftField.divideBy b g
   (Continuous.measurable (HolderWith.continuous hg hβ)) c hc₀ hg₀
local notation "q" => ScalarDriftNativeDirection.row bθ (Function.uncurry W)

/-- The cross correction for a possibly signed time multiplier is exactly
the corresponding stopped Bochner drift coordinate. -/
theorem correction (ht : t≤H) (u : Lp Noise 2 νin)
    (hu : u =ᵐ[νin] fun p => a p.1 p.2 • q p)
    (ham : ∀ ω,Measurable (fun s => a s ω)) (ha : ∀ s ω,|a s ω|≤1) :
    NativeCrossEnergy.cross (FiniteCylindricalIto.processTransport v) u =ᵐ[μ]
      fun ω => φ ψ n (ScalarStoppedDriftConvolution.convolution b W a N ω t) := by
  classical
  have hv := raw_row F μ H W hW hc hg hβ hβ₁ N t ψ n
  let f₀ (p : ℝ≥0×Ω) := inner ℝ ((FiniteCylindricalIto.processTransport v) p) (u p)
  let f₁ (p : ℝ≥0×Ω) := inner ℝ (row p) (a p.1 p.2 • q p)
  have hpair : f₀ =ᵐ[(tm H).prod μ] f₁ := by
    have hh : f₀ =ᵐ[νin] f₁ :=
      (hv.and hu).mono (fun p h => congrArg₂ (inner ℝ) h.1 h.2)
    rw [NativeRowRepresentatives.inputMeasure_eq] at hh
    exact ae_eq_of_ae_eq_trim hh
  have hFibre := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := tm H)).quasiMeasurePreserving.ae hpair)
  filter_upwards [hFibre] with ω hω
  have hsame : MathFin.ItoIntegralCLM.timeMeasure_T H = tm H := by
    exact (SHEStochastic.timeMeasure_eq H).symm
  change (∀ᵐ s ∂tm H,f₀ (s,ω)=f₁ (s,ω)) at hω
  change (∫ s,f₀ (s,ω) ∂MathFin.ItoIntegralCLM.timeMeasure_T H) = _
  rw [hsame,integral_congr_ae hω,ScalarStoppedDriftFourier.coordinate b W hc a N ω (ham ω) (fun s => ha s ω) t ψ n]
  let f (s : ℝ≥0) := if (s : ℝ)<t ∧ (s : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω then
    Real.exp (-((t : ℝ)-(s : ℝ))*(n : ℝ)^2)*a s ω*
      φ ψ n (ScalarLinearGrowthDriftField.field b (s,W s ω)) else 0
  change (∫ s,inner ℝ (row (s,ω)) (a s ω • q (s,ω)) ∂tm H) = ∫ s,f s ∂tm t
  rw [←timeMeasure_restrict ht,←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with s hs
  by_cases h : (s : ℝ)<t ∧ (s : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω
  · have hmem : (s,ω) ∈ ScalarStoppedHeatFourierInput.before W N t := h
    have hJ : s∈Ioc 0 t := ⟨hs.1,(NNReal.coe_lt_coe.mp h.1).le⟩
    rw [ScalarStoppedHeatFourierInput.row,indicator_of_mem hmem,indicator_of_mem hJ]
    simp only [f,ite_eq_left h,real_inner_smul_left,real_inner_smul_right,
      UnboundedNativeHeatEquation.physical,ScalarDriftNativeDirection.row,Function.uncurry]
    rw [ScalarGirsanovDriftPairing.fourier b hg hβ hβ₁ c hc₀ hg₀ s (W s ω) ψ n]
    ring
  · have hmem : (s,ω) ∉ ScalarStoppedHeatFourierInput.before W N t := h
    rw [ScalarStoppedHeatFourierInput.row,indicator_of_notMem hmem,inner_zero_left]
    by_cases hJ : s∈Ioc 0 t
    · simp only [indicator_of_mem hJ,f,ite_eq_right h]
    · exact (indicator_of_notMem hJ _).symm

end SHEStochastic.ScalarStoppedHeatCross
