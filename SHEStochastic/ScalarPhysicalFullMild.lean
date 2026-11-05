module

public import SHEStochastic.ScalarPhysicalMoment
public import SHEStochastic.ScalarPhysicalFullLocality

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalFullMild
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarStatePathFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "tm" => PredictableL2.timeMeasure
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω : Type*} {H : ℝ≥0} (b : ScalarLinearGrowthDriftField.Data H)
  (W : ℝ≥0→Ω→RealL2)

def drift (t : ℝ≥0) (ω : Ω) : RealL2 :=
  ∫ s : ℝ≥0,RealHeat.realHeat ((t : ℝ)-(s : ℝ))
    (ScalarLinearGrowthDriftField.field b (s,W s ω)) ∂tm t

theorem drift_before (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (h : (t : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω) :
    ScalarPhysicalDriftClock.physicalConvolution b W N ω t=drift b W t ω := by
  apply integral_congr_ae
  filter_upwards [timeMeasure_ae_mem t] with s hs
  have h' : (s : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω :=
    lt_of_le_of_lt (WithTop.coe_le_coe.mpr hs.2) h
  simp only [ScalarStoppedDriftConvolution.input,ite_eq_left h',one_smul]

variable [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (u₀ : RealL2)

/-- The physical Fourier mild equation at every fixed time, on the
whole probability space. Both the drift integral and the original
white-noise row use the full interval up to that time. -/
def Equation (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H) : Prop :=
  ∀ (t : ℝ≥0),t≤H → ∀ (ψ : ℂ →L[ℝ] ℝ) (n : ℤ),
    ∃ v : Process (E := Noise) F μ H,
      v=ᵐ[energyMeasure μ H] ScalarPhysicalFullInput.row W hg hβ hβ₁ t ψ n ∧
      (fun ω => φ ψ n (W t ω-RealHeat.realHeat (t : ℝ) u₀-drift b W t ω)) =ᵐ[μ] J.integral v

variable {I : Type*} [Countable I] [DecidableEq I]
  (P : FiniteScalarIto.Family F μ H I) (e : HilbertBasis I ℝ Noise)
  (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω)) (hn : NullCompleteFiltration.ContainsNullSets F μ)

local notation "J" => FiniteCylindricalIto.terminalIto P.toCoordinates e

include hW hc hn in
/-- Exhaust the genuine state exits once the uncut row has been
constructed from the original integrated second moment. -/
theorem of_stopped
    (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H))
    (hEq : ScalarPhysicalStoppedEquation.Equation F μ H hg hβ hβ₁ b u₀ W J) :
    Equation b W F μ hg hβ hβ₁ u₀ J := by
  intro t ht ψ n
  let w := ScalarPhysicalFullInput.input F μ H W hW hg hβ hβ₁ t ψ n hM
  have hw := ScalarPhysicalFullInput.input_ae F μ H W hW hg hβ hβ₁ t ψ n hM
  have ha (N : ℕ) : ∀ᵐ ω ∂μ,(t : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω →
      φ ψ n (W t ω-RealHeat.realHeat (t : ℝ) u₀-drift b W t ω)=(J).integral w ω := by
    obtain ⟨v,hv,he⟩ := hEq N t ht ψ n
    have hi := ScalarPhysicalFullLocality.compare F μ H W hW hc hg hβ hβ₁ N t ψ n
      P e hn v w hv hw
    filter_upwards [he,hi] with ω he hi hω
    rw [←drift_before b W N t ω hω]
    exact (he hω).trans (hi hω)
  refine ⟨w,hw,?_⟩
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  have htop := ContinuousNormExit.tendsto_top W hc ω
  rw [WithTop.tendsto_nhds_top_iff] at htop
  obtain ⟨N,hN⟩ := (htop t).exists
  exact hω N hN

include hW hc hn in
/-- Every full physical weak mild solution satisfies the stopped
formulation used for localization. -/
theorem to_stopped (hEq : Equation b W F μ hg hβ hβ₁ u₀ J) :
    ScalarPhysicalStoppedEquation.Equation F μ H hg hβ hβ₁ b u₀ W J := by
  intro N t ht ψ n
  obtain ⟨w,hw,he⟩ := hEq t ht ψ n
  obtain ⟨v,hv⟩ := ScalarPhysicalFullLocality.exists_cut F μ H W hW hc hg hβ hβ₁ N t ψ n w hw
  have hi := ScalarPhysicalFullLocality.compare F μ H W hW hc hg hβ hβ₁ N t ψ n
    P e hn v w hv hw
  refine ⟨v,hv,?_⟩
  filter_upwards [he,hi] with ω he hi hω
  rw [drift_before b W N t ω hω]
  exact he.trans (hi hω).symm

end SHEStochastic.ScalarPhysicalFullMild
