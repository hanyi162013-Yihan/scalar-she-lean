module

public import SHEStochastic.ScalarPhysicalFullMild
public import SHEStochastic.ScalarTheoremOneTwo

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalFullLaw
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarStatePathFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local notation "e" => ScalarUnboundedFourierProjection.basis
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable (H : ℝ≥0) {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)

/-- Continuous weak solution of the original unit-torus equation,
with the ordinary unstopped Fourier mild identity. -/
structure Solution (Ω : Type) [MeasurableSpace Ω] where
  μ : Measure Ω
  [probability : IsProbabilityMeasure μ]
  F : Filtration ℝ≥0 ‹MeasurableSpace Ω›
  W : ℝ≥0 → Ω → RealL2
  predictable : StronglyMeasurable[F.predictable] (Function.uncurry W)
  continuous : ∀ ω,Continuous (fun t => W t ω)
  nulls : NullCompleteFiltration.ContainsNullSets F μ
  P : FiniteScalarIto.Family F μ H (Fin 1 × HaarNode)
  initial : W 0=ᵐ[μ] fun _ => u₀
  equation : ScalarPhysicalFullMild.Equation b W F μ hg hβ hβ₁ u₀
    (FiniteCylindricalIto.terminalIto P.toCoordinates e)

attribute [instance] Solution.probability

def Solution.of_stopped {Ω : Type} [MeasurableSpace Ω]
    (S : ScalarPhysicalDriftedLaw.Solution H hg hβ hβ₁ b u₀ e Ω) :
    Solution H hg hβ hβ₁ b u₀ Ω :=
  ⟨S.μ,S.F,S.W,S.predictable,S.continuous,S.nulls,S.P,S.initial,
    ScalarPhysicalFullMild.of_stopped b S.W S.F S.μ hg hβ hβ₁ u₀ S.P e S.predictable S.continuous S.nulls
      (ScalarPhysicalMoment.integrable_sq H hg hβ hβ₁ b u₀ e S) S.equation⟩

def Solution.to_stopped {Ω : Type} [MeasurableSpace Ω] (S : Solution H hg hβ hβ₁ b u₀ Ω) :
    ScalarPhysicalDriftedLaw.Solution H hg hβ hβ₁ b u₀ e Ω :=
  ⟨S.μ,S.F,S.W,S.predictable,S.continuous,S.nulls,S.P,S.initial,
    ScalarPhysicalFullMild.to_stopped b S.W S.F S.μ hg hβ hβ₁ u₀ S.P e S.predictable S.continuous S.nulls S.equation⟩

variable (g)

/-- The law of an ordinary physical scalar weak mild solution. -/
def Realizes (law : Measure (Space H)) : Prop :=
  ∃ (C β : ℝ≥0) (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
    (Ω : Type) (m : MeasurableSpace Ω) (S : @Solution H g C β hg hβ hβ₁ b u₀ Ω m),
    S.μ.map (NativeContinuousPath.path H S.W S.continuous)=law

theorem realizes_iff (law : Measure (Space H)) :
    Realizes H g b u₀ law ↔ ScalarTheoremOneTwo.Realizes H g b u₀ law := by
  constructor
  · rintro ⟨C,β,hg,hβ,hβ₁,Ω,m,S,he⟩
    let _ : MeasurableSpace Ω := m
    exact ⟨C,β,hg,hβ,hβ₁,Ω,m,S.to_stopped H hg hβ hβ₁ b u₀,he⟩
  · rintro ⟨C,β,hg,hβ,hβ₁,Ω,m,S,he⟩
    let _ : MeasurableSpace Ω := m
    exact ⟨C,β,hg,hβ,hβ₁,Ω,m,Solution.of_stopped H hg hβ hβ₁ b u₀ S,he⟩

end SHEStochastic.ScalarPhysicalFullLaw
