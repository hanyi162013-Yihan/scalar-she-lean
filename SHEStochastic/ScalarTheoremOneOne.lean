module

public import SHEStochastic.ScalarUnitTorusBoundedExistence
public import SHEStochastic.ScalarUnitTorusBoundedUniqueness
public import SHEStochastic.VectorWhiteCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarTheoremOneOne
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.StoppedFourier SHE.FiniteHaar
  AddCircle UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local notation "Noise" => ScalarVarianceNormalization.Noise
local notation "ν₂" => haarAddCircle (T := 2*Real.pi)

/-- Fix an explicit scalar orthonormal white-noise basis. -/
def noiseBasis : HilbertBasis HaarNode ℝ Noise :=
  HilbertBasis.ofRepr (NativePhysicalState.equivalence.symm.trans VectorWhiteCoordinates.scalar)

private theorem row_eq {Ω : Type} (H : ℝ≥0) (W : ℝ≥0 → Ω → RealL2)
    {g : ℝ → ℝ} {C D β γ : ℝ≥0} (hg : HolderWith C β g) (hg' : HolderWith D γ g)
    (hβ : 0<β) (hβ₁ : β≤1) (hγ : 0<γ) (hγ₁ : γ≤1)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ScalarUnitTorusFourierClock.row H W hg hβ hβ₁ a n =
    ScalarUnitTorusFourierClock.row H W hg' hγ hγ₁ a n := by
  funext p
  apply congrArg (fun u : Noise =>
    Real.exp ((NativeClock.rate : ℝ)*min (p.1 : ℝ) (H : ℝ)*(n : ℝ)^2) • u)
  apply Lp.ext
  exact (StateNoiseCovariance.row_ae ν₂ hβ hβ₁ hg (NativeFourierHeatCoordinate.weight a n)
    (physical W p)).trans (StateNoiseCovariance.row_ae ν₂ hγ hγ₁ hg'
      (NativeFourierHeatCoordinate.weight a n) (physical W p)).symm

private theorem equation_change_holder {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (W : ℝ≥0 → Ω → RealL2) (P : FiniteScalarIto.Family F μ H HaarNode)
    {g : ℝ → ℝ} {C D β γ : ℝ≥0} (hg : HolderWith C β g) (hg' : HolderWith D γ g)
    (hβ : 0<β) (hβ₁ : β≤1) (hγ : 0<γ) (hγ₁ : γ≤1)
    (he : ScalarUnitTorusFourierEquation.Equation F μ H noiseBasis W hg hβ hβ₁ P (W 0)) :
    ScalarUnitTorusFourierEquation.Equation F μ H noiseBasis W hg' hγ hγ₁ P (W 0) := by
  intro a n
  obtain ⟨v,hv,heq⟩ := he a n
  refine ⟨v,?_,heq⟩
  rw [←row_eq H W hg hg' hβ hβ₁ hγ hγ₁]
  exact hv

/-- Law of a continuous weak scalar mild realization, formulated on
the full collection of Fourier test rows of the unit-torus equation. -/
def Realizes (H : ℝ≥0) (g : ℝ → ℝ) (u₀ : RealL2) (law : Measure (StoppedPathPasting.Path H RealL2)) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (F : Filtration ℝ≥0 m) (μ : @Measure Ω m),
    ∃ (_ : IsProbabilityMeasure μ) (P : FiniteScalarIto.Family F μ H HaarNode) (W : ℝ≥0 → Ω → RealL2)
      (hc : ∀ ω,Continuous (fun t => W t ω)),
      StronglyMeasurable[F.predictable] (Function.uncurry W) ∧
      NullCompleteFiltration.ContainsNullSets F μ ∧
      (W 0 =ᵐ[μ] fun _ => u₀) ∧
      (∃ (C β : ℝ≥0) (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1),
        ScalarUnitTorusFourierEquation.Equation F μ H noiseBasis W hg hβ hβ₁ P (W 0)) ∧
      μ.map (NativeContinuousPath.path H W hc)=law

/-- Manuscript Theorem 1.1 in the stochastic Fourier mild formulation. -/
theorem theorem_1_1 (H : ℝ≥0) (hH : 0<H)
    {g : ℝ → ℝ} {C β₀ : ℝ≥0} (hg : HolderWith C β₀ g) (hβ₀ : 0<β₀)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B) (c : ℝ) (hc : 0<c) (hell : ∀ z,c≤|g z|)
    (u₀ : RealL2) :
    ∃! law, Realizes H g u₀ law := by
  obtain ⟨C',β,hβ,hβ₁,hg'⟩ := ScalarBoundedWellPosed.effective_exponent hg hβ₀ B hb
  obtain ⟨Ω,m,F,μ,hμ,P,W,hW,hcW,hnW,hiW,heW⟩ :=
    ScalarUnitTorusBoundedExistence.exists_solution H hH hg' hβ hβ₁ B hb c hc hell noiseBasis u₀
  let _ : MeasurableSpace Ω := m
  let _ : IsProbabilityMeasure μ := hμ
  let law := μ.map (NativeContinuousPath.path H W hcW)
  refine ⟨law,⟨Ω,m,F,μ,hμ,P,W,hcW,hW,hnW,hiW,⟨C',β,hg',hβ,hβ₁.le,heW⟩,rfl⟩,?_⟩
  rintro other ⟨Ξ,mΞ,G,ν,hν,Q,Z,hcZ,hZ,hnZ,hiZ,⟨D,γ,hg'',hγ,hγ₁,heZ⟩,hLaw⟩
  let _ : MeasurableSpace Ξ := mΞ
  let _ : IsProbabilityMeasure ν := hν
  have heZ' := equation_change_holder G ν H Z Q hg'' hg' hγ hγ₁ hβ hβ₁.le heZ
  exact hLaw.symm.trans (ScalarUnitTorusBoundedUniqueness.laws_eq G F ν μ H hH hg' hβ hβ₁
    B hb c hc hell noiseBasis u₀ Q P Z W hZ hW hcZ hcW hnZ hnW hiZ hiW heZ' heW)

end SHEStochastic.ScalarTheoremOneOne
