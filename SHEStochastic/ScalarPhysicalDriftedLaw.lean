module

public import SHEStochastic.ScalarPhysicalStoppedEquation
public import SHEStochastic.ScalarDriftedNativeLaw
public import SHEStochastic.NativeInverseTimeDilatedFamily
public import SHEStochastic.ScalarUnitTorusStateClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalDriftedLaw
open MeasureTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarStatePathFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos
local notation "clk" => clock r hr
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable (H : ℝ≥0) {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
  {ι : Type} [Countable ι] [DecidableEq ι] (e : HilbertBasis ι ℝ Noise)

structure Solution (Ω : Type) [MeasurableSpace Ω] where
  μ : Measure Ω
  [probability : IsProbabilityMeasure μ]
  F : Filtration ℝ≥0 ‹MeasurableSpace Ω›
  W : ℝ≥0 → Ω → RealL2
  predictable : StronglyMeasurable[F.predictable] (Function.uncurry W)
  continuous : ∀ ω,Continuous (fun t => W t ω)
  nulls : NullCompleteFiltration.ContainsNullSets F μ
  P : FiniteScalarIto.Family F μ H ι
  initial : W 0 =ᵐ[μ] fun _ => u₀
  equation : ScalarPhysicalStoppedEquation.Equation F μ H hg hβ hβ₁ b u₀ W
    (FiniteCylindricalIto.terminalIto P.toCoordinates e)

attribute [instance] Solution.probability

/-- A weak solution of the physical scalar equation gives its continuous
L² state-path law on the original unit-torus time interval. -/
def Realizes (law : Measure (Space H)) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (S : @Solution H g C β hg hβ hβ₁ b u₀ ι _ _ e Ω m),
    S.μ.map (NativeContinuousPath.path H S.W S.continuous)=law

local notation "hnG" => ScalarUnitTorusFourierClock.holder hg
local notation "bn" => ScalarPhysicalDriftClock.native b
local notation "Native" => ScalarDriftedNativeLaw.Solution (r*H) hnG hβ hβ₁ bn u₀ e

private theorem path_measure {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : ℝ≥0→Ω→RealL2) (hU : Measurable (Function.uncurry U))
    (hc : ∀ ω,Continuous (fun t => U t ω)) :
    (μ.map (NativeContinuousPath.path (r*H) U hc)).map (ScalarUnitTorusStateClock.pull H) =
      μ.map (NativeContinuousPath.path H (pullPath r hr U) (pullPath_continuous r hr U hc)) := by
  rw [Measure.map_map (ScalarUnitTorusStateClock.measurable_pull H)
    (NativeContinuousPath.measurable_path (r*H) U hc hU),ScalarUnitTorusStateClock.path_pull]

theorem from_native {Ω : Type} [MeasurableSpace Ω] (N : Native Ω) :
    ∃ S : Solution H hg hβ hβ₁ b u₀ e Ω,
      S.μ.map (NativeContinuousPath.path H S.W S.continuous) =
        (N.μ.map (NativeContinuousPath.path (r*H) N.W N.continuous)).map (ScalarUnitTorusStateClock.pull H) := by
  let _ : SecondCountableTopology Noise := e.repr.toHomeomorph.secondCountableTopology
  let F := filtration N.F (clk).symm
  have hF : filtration F (clk)=N.F := filtration_inverse_clock r hr N.F
  have hPair : ∀ (Q : FiniteScalarIto.Family (filtration F (clk)) N.μ (r*H) ι)
      (hU : StronglyMeasurable[(filtration F (clk)).predictable] (Function.uncurry N.W)),
      NullCompleteFiltration.ContainsNullSets (filtration F (clk)) N.μ →
      ScalarStoppedMildMoment.Equation (filtration F (clk)) N.μ (r*H) N.W hU N.continuous
        hnG hβ hβ₁ (FiniteCylindricalIto.terminalIto Q.toCoordinates e) bn (fun _ _ => 1) u₀ →
      ∃ P : FiniteScalarIto.Family F N.μ H ι,
        StronglyMeasurable[F.predictable] (Function.uncurry (pullPath r hr N.W)) ∧
        NullCompleteFiltration.ContainsNullSets F N.μ ∧
        ScalarPhysicalStoppedEquation.Equation F N.μ H hg hβ hβ₁ b u₀ (pullPath r hr N.W)
          (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
    intro Q hU hnull hEq
    obtain ⟨P,hP⟩ := NativeInverseTimeDilatedFamily.exists_family F N.μ r hr H Q e hnull
    exact ⟨P,pullPath_predictable F r hr N.W hU,InverseClockLocality.null_complete F N.μ r hr hnull,
      (ScalarPhysicalStoppedEquation.iff_native F N.μ H hg hβ hβ₁ b u₀ N.W hU N.continuous
        (FiniteCylindricalIto.terminalIto Q.toCoordinates e)
        (FiniteCylindricalIto.terminalIto P.toCoordinates e) hP).mpr hEq⟩
  rw [hF] at hPair
  obtain ⟨P,hPred,hNull,hEq⟩ := hPair N.P N.predictable N.nulls N.equation
  have hi : pullPath r hr N.W 0 =ᵐ[N.μ] fun _ => u₀ := by
    change N.W (r*0) =ᵐ[N.μ] _
    rw [mul_zero]
    exact N.initial
  let S : Solution H hg hβ hβ₁ b u₀ e Ω := ⟨N.μ,F,pullPath r hr N.W,hPred,
    pullPath_continuous r hr N.W N.continuous,hNull,P,hi,hEq⟩
  exact ⟨S,(path_measure H N.μ N.W (N.predictable.mono (predictable_le_product N.F)).measurable
    N.continuous).symm⟩

theorem to_native {Ω : Type} [MeasurableSpace Ω] (S : Solution H hg hβ hβ₁ b u₀ e Ω) :
    ∃ N : Native Ω,
      S.μ.map (NativeContinuousPath.path H S.W S.continuous) =
        (N.μ.map (NativeContinuousPath.path (r*H) N.W N.continuous)).map (ScalarUnitTorusStateClock.pull H) := by
  let _ : SecondCountableTopology Noise := e.repr.toHomeomorph.secondCountableTopology
  let U := ScalarUnitTorusStateClock.native S.W
  let hU := ScalarUnitTorusStateClock.predictable S.F S.W S.predictable
  let hc := ScalarUnitTorusStateClock.continuous_native S.W S.continuous
  obtain ⟨Q,hQ⟩ := NativeTimeDilatedFamily.exists_family S.F S.μ r hr H S.P e S.nulls
  have hPhys : ScalarPhysicalStoppedEquation.Equation S.F S.μ H hg hβ hβ₁ b u₀ (pullPath r hr U)
      (FiniteCylindricalIto.terminalIto S.P.toCoordinates e) := by
    rw [ScalarUnitTorusStateClock.pull_native]
    exact S.equation
  have hN := (ScalarPhysicalStoppedEquation.iff_native S.F S.μ H hg hβ hβ₁ b u₀ U hU hc
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e)
    (FiniteCylindricalIto.terminalIto S.P.toCoordinates e) hQ).mp hPhys
  have hInit : U 0 =ᵐ[S.μ] fun _ => u₀ := by
    change ScalarUnitTorusStateClock.native S.W 0 =ᵐ[S.μ] _
    rw [ScalarUnitTorusStateClock.native_zero]
    exact S.initial
  let N : Native Ω := ⟨S.μ,filtration S.F (clk),U,hU,hc,
    containsNullSets S.F (clk) S.μ S.nulls,Q,hInit,hN⟩
  refine ⟨N,?_⟩
  have h := path_measure H S.μ U (hU.mono (predictable_le_product (filtration S.F (clk)))).measurable hc
  have hp : NativeContinuousPath.path H (pullPath r hr U) (pullPath_continuous r hr U hc) =
      NativeContinuousPath.path H S.W S.continuous := by
    funext ω
    apply ContinuousMap.ext
    intro t
    exact congrFun (congrFun (ScalarUnitTorusStateClock.pull_native S.W) t.val.toNNReal) ω
  rw [hp] at h
  exact h.symm

theorem exists_unique
    (hN : ∃! law,ScalarDriftedNativeLaw.Realizes (r*H) hnG hβ hβ₁ bn u₀ e law) :
    ∃! law,Realizes H hg hβ hβ₁ b u₀ e law := by
  obtain ⟨ρ,⟨Ω,m,N,hρ⟩,hUnique⟩ := hN
  let _ : MeasurableSpace Ω := m
  obtain ⟨S,hS⟩ := from_native H hg hβ hβ₁ b u₀ e N
  refine ⟨ρ.map (ScalarUnitTorusStateClock.pull H),⟨Ω,m,S,?_⟩,?_⟩
  · exact hS.trans (congrArg (fun q : Measure (Space (r*H)) => q.map (ScalarUnitTorusStateClock.pull H)) hρ)
  · rintro q ⟨Ξ,mΞ,T,hT⟩
    let _ : MeasurableSpace Ξ := mΞ
    obtain ⟨N',hN'⟩ := to_native H hg hβ hβ₁ b u₀ e T
    have hh := hUnique _ ⟨Ξ,mΞ,N',rfl⟩
    rw [←hT,hN',hh]

end SHEStochastic.ScalarPhysicalDriftedLaw
