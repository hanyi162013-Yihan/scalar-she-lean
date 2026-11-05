module

public import SHEStochastic.ScalarCanonicalLikelihood
public import SHEStochastic.ScalarReverseDensity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarDriftedNativeLaw
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarCanonicalObservation ScalarStatePathFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

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
  equation : ScalarStoppedMildMoment.Equation F μ H W predictable continuous hg hβ hβ₁
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) b (fun _ _ => 1) u₀

attribute [instance] Solution.probability

def Realizes (law : Measure (Space H)) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (S : @Solution H g C β hg hβ hβ₁ b u₀ ι _ _ e Ω m),
    S.μ.map (NativeContinuousPath.path H S.W S.continuous)=law

/-- This is precisely the drift-free law comparison used in the
Girsanov reduction. The same fixed noise basis is used throughout. -/
def ZeroUnique : Prop :=
  ∀ {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (M : Model H hg hβ hβ₁ b u₀ Ω ι) (N : Model H hg hβ hβ₁ b u₀ Ξ ι),
    M.basis=e → N.basis=e →
    (M.W 0 =ᵐ[M.μ] fun _ => u₀) → (N.W 0 =ᵐ[N.μ] fun _ => u₀) →
    M.μ.map M.path=N.μ.map N.path

variable {H hg hβ hβ₁ b u₀ e}
variable (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)

private theorem nulls_of_equivalent {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) {μ η : Measure Ω} (hμ : μ ≪ η)
    (hn : NullCompleteFiltration.ContainsNullSets F μ) : NullCompleteFiltration.ContainsNullSets F η :=
  fun t A hA => hn t A (hμ hA)

include hc hell in
theorem exists_of_zero {Ω : Type} [MeasurableSpace Ω]
    (M : Model H hg hβ hβ₁ b u₀ Ω ι) (hBasis : M.basis=e)
    (hInit : M.W 0 =ᵐ[M.μ] fun _ => u₀) : Nonempty (Solution H hg hβ hβ₁ b u₀ e Ω) := by
  obtain ⟨u,_,hQ,R,hQμ,hμQ,hEq,_⟩ := ScalarLinearGrowthGirsanov.change M.F M.μ H M.P M.basis
    M.W M.predictable M.continuous hg hβ hβ₁ b c hc hell u₀ M.nulls false M.equation
  refine ⟨⟨_,M.F,M.W,M.predictable,M.continuous,
    nulls_of_equivalent M.F hμQ M.nulls,R,hQμ.ae_eq hInit,?_⟩⟩
  simpa only [←hBasis,ScalarLinearGrowthGirsanov.present,Bool.not_false,ite_true] using hEq

include hc hell in
theorem laws_eq {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (hZero : ZeroUnique H hg hβ hβ₁ b u₀ e)
    (A : Solution H hg hβ hβ₁ b u₀ e Ω) (B : Solution H hg hβ hβ₁ b u₀ e Ξ) :
    A.μ.map (NativeContinuousPath.path H A.W A.continuous) =
      B.μ.map (NativeContinuousPath.path H B.W B.continuous) := by
  obtain ⟨u,hu,hQ,R,hQμ,hμQ,hEq,hIto⟩ := ScalarLinearGrowthGirsanov.change A.F A.μ H A.P e
    A.W A.predictable A.continuous hg hβ hβ₁ b c hc hell u₀ A.nulls true A.equation
  obtain ⟨v,hv,hQ',R',hQν,hνQ,hEq',hIto'⟩ := ScalarLinearGrowthGirsanov.change B.F B.μ H B.P e
    B.W B.predictable B.continuous hg hβ hβ₁ b c hc hell u₀ B.nulls true B.equation
  let M : Model H hg hβ hβ₁ b u₀ Ω ι := ⟨_,A.F,A.W,A.predictable,A.continuous,
    nulls_of_equivalent A.F hμQ A.nulls,R,e,hEq⟩
  let N : Model H hg hβ hβ₁ b u₀ Ξ ι := ⟨_,B.F,B.W,B.predictable,B.continuous,
    nulls_of_equivalent B.F hνQ B.nulls,R',e,hEq'⟩
  let ρ := M.μ.map M.path
  let _ : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map_iff M.path_measurable.aemeasurable |>.2 inferInstance
  have hN : N.μ.map N.path=ρ := (hZero M N rfl rfl (hQμ.ae_eq A.initial) (hQν.ae_eq B.initial)).symm
  let θ := ScalarLinearGrowthDriftField.divideBy b g (HolderWith.continuous hg hβ).measurable c hc hell
  have h₀ (z : ℝ) : g z≠0 := abs_pos.mp ((show (0 : ℝ)<c from hc).trans_le (hell z))
  obtain ⟨w,w',D,hw,hw',hmD,hDM,hDN⟩ := ScalarCanonicalLikelihood.exists_common θ M ρ rfl N hN h₀
  have hμin : FiniteScalarIto.inputMeasure A.F A.μ H ≪ FiniteScalarIto.inputMeasure M.F M.μ H := by
    simp only [NativeRowRepresentatives.inputMeasure_eq,energyMeasure]
    exact ((Measure.AbsolutelyContinuous.rfl : PredictableL2.timeMeasure H ≪ PredictableL2.timeMeasure H).prod hμQ).trim _
  have hνin : FiniteScalarIto.inputMeasure B.F B.μ H ≪ FiniteScalarIto.inputMeasure N.F N.μ H := by
    simp only [NativeRowRepresentatives.inputMeasure_eq,energyMeasure]
    exact ((Measure.AbsolutelyContinuous.rfl : PredictableL2.timeMeasure H ≪ PredictableL2.timeMeasure H).prod hνQ).trim _
  have hu' : u =ᵐ[FiniteScalarIto.inputMeasure A.F A.μ H] w := by
    apply hu.trans _
    simpa only [ScalarLinearGrowthGirsanov.sign,ite_true,one_smul,θ,M] using (hμin.ae_eq hw).symm
  have hv' : v =ᵐ[FiniteScalarIto.inputMeasure B.F B.μ H] w' := by
    apply hv.trans _
    simpa only [ScalarLinearGrowthGirsanov.sign,ite_true,one_smul,θ,N] using (hνin.ae_eq hw').symm
  have hA := ScalarReverseDensity.inverse A.P e u R w hu' (hIto u w hu')
  have hB := ScalarReverseDensity.inverse B.P e v R' w' hv' (hIto' v w' hv')
  have hl := ScalarCanonicalDensityLimit.map_tilt M.path_measurable D hmD _ hDM
  have hr := ScalarCanonicalDensityLimit.map_tilt N.path_measurable D hmD _ hDN
  change A.μ.map M.path = B.μ.map N.path
  conv_lhs => rw [hA]
  conv_rhs => rw [hB]
  exact hl.trans ((congrArg (fun m : Measure (Space H) => m.withDensity D) hN).symm.trans hr.symm)

end SHEStochastic.ScalarDriftedNativeLaw
