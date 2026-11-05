module

public import SHEStochastic.ScalarStoppedHeatCross
public import SHEStochastic.ScalarStoppedDriftAlgebra
public import SHEStochastic.ScalarStoppedMildMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedEquationTransport
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

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ η : Measure Ω)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure η] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family F η H ι)
  (e : HilbertBasis ι ℝ Noise)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (b : ScalarLinearGrowthDriftField.Data H) (c : ℝ≥0) (hc₀ : 0<c) (hg₀ : ∀ z,(c : ℝ)≤|g z|)
  (u₀ : RealL2)

local notation "νin" m:max => FiniteScalarIto.inputMeasure F m H
local notation "J" m:max => FiniteCylindricalIto.terminalIto (FiniteScalarIto.Family.toCoordinates m) e
local notation "I" m:max => FiniteCylindricalIto.rawIntegral (FiniteScalarIto.Family.toCoordinates m) e
local notation "bθ" => ScalarLinearGrowthDriftField.divideBy b g
  (Continuous.measurable (HolderWith.continuous hg hβ)) c hc₀ hg₀
local notation "rowθ" => ScalarDriftNativeDirection.row bθ (Function.uncurry W)
local notation "φ" => NativeFourierHeatCoordinate.coordinate

/-- Apply the compatible stochastic transport to the actual stopped heat
row. The sign is fixed by the shifted Brownian integral, and the drift
multiplier changes from a to a minus the shift. -/
theorem transport (hη : η ≪ μ) (hμ : μ ≪ η)
    (u : Lp Noise 2 (νin μ)) (a d : ℝ≥0 → Ω → ℝ)
    (hu : u =ᵐ[νin μ] fun p => d p.1 p.2 • rowθ p)
    (ham : ∀ ω,Measurable (fun s => a s ω)) (ha : ∀ s ω,|a s ω|≤1)
    (hdm : ∀ ω,Measurable (fun s => d s ω)) (hd : ∀ s ω,|d s ω|≤1)
    (hIto : ∀ (v : Lp Noise 2 (νin μ)) (w : Lp Noise 2 (νin η)),v =ᵐ[νin μ] w →
      (I Q) w =ᵐ[η] (fun ω => (I P) v ω+NativeCrossEnergy.cross v u ω))
    (hEq : ScalarStoppedMildMoment.Equation F μ H W hW hc hg hβ hβ₁ (J P) b a u₀) :
    ScalarStoppedMildMoment.Equation F η H W hW hc hg hβ hβ₁ (J Q) b (fun s ω => a s ω-d s ω) u₀ := by
  intro N t ht ψ n
  let v (m : Measure Ω) [IsProbabilityMeasure m] :=
    ScalarStoppedHeatFourierInput.input F m H W hW hc hg hβ hβ₁ N t ψ n
  let vm := FiniteCylindricalIto.processTransport (v μ)
  let ve := FiniteCylindricalIto.processTransport (v η)
  have hve := ScalarStoppedHeatCross.raw_row F η H W hW hc hg hβ hβ₁ N t ψ n
  have hvm := ScalarStoppedHeatCross.raw_row F μ H W hW hc hg hβ hβ₁ N t ψ n
  have hCross := ScalarStoppedHeatCross.correction F μ H W hW hc hg hβ hβ₁ N t ψ n
    b c hc₀ hg₀ d ht u hu hdm hd
  have hback : νin μ ≪ νin η := by
    simp only [NativeRowRepresentatives.inputMeasure_eq,energyMeasure]
    exact ((Measure.AbsolutelyContinuous.rfl : PredictableL2.timeMeasure H ≪ PredictableL2.timeMeasure H).prod hμ).trim _
  have heq : vm =ᵐ[νin μ] ve := hvm.trans (hback.ae_eq hve).symm
  have hI := hIto vm ve heq
  filter_upwards [hI,hη.ae_eq hCross,hη.ae_le (hEq N t ht ψ n)] with ω hI hCross hM hN
  have hM' := hM hN
  let D (x : ℝ≥0 → Ω → ℝ) := ScalarStoppedDriftConvolution.convolution b W x N ω t
  have hD : D (fun s ω => a s ω-d s ω)=D a-D d :=
    ScalarStoppedDriftAlgebra.sub b W hc N ω t a d (ham ω) (fun s => ha s ω) (hdm ω) (fun s => hd s ω)
  change φ ψ n (W t ω-NativeHeatObservation.heat (t : ℝ) u₀-D (fun s ω => a s ω-d s ω)) = (I Q) ve ω
  change φ ψ n (W t ω-NativeHeatObservation.heat (t : ℝ) u₀-D a) = (I P) vm ω at hM'
  change NativeCrossEnergy.cross vm u ω = φ ψ n (D d) at hCross
  rw [hI,hCross,hD]
  simp only [map_sub] at hM' ⊢
  linarith only [hM']

end SHEStochastic.ScalarStoppedEquationTransport
