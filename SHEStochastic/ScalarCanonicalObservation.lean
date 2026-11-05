module

public import SHEStochastic.ScalarFourierPredictableSpan
public import SHEStochastic.ScalarStatePathFiltration
public import SHEStochastic.ScalarStoppedMomentUniform

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarCanonicalObservation
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarStatePathFiltration
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

/-- A drift-free model for the actual continuous stopped Fourier equation.
The moment condition will be derived from its equation. -/
structure Model (Ω ι : Type*) [MeasurableSpace Ω] [Countable ι] [DecidableEq ι] where
  μ : Measure Ω
  [probability : IsProbabilityMeasure μ]
  F : Filtration ℝ≥0 ‹MeasurableSpace Ω›
  W : ℝ≥0 → Ω → RealL2
  predictable : StronglyMeasurable[F.predictable] (Function.uncurry W)
  continuous : ∀ ω,Continuous (fun t => W t ω)
  nulls : NullCompleteFiltration.ContainsNullSets F μ
  P : FiniteScalarIto.Family F μ H ι
  basis : HilbertBasis ι ℝ Noise
  equation : ScalarStoppedMildMoment.Equation F μ H W predictable continuous hg hβ hβ₁
    (FiniteCylindricalIto.terminalIto P.toCoordinates basis) b (fun _ _ => 0) u₀

attribute [instance] Model.probability

variable {H hg hβ hβ₁ b u₀}
variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (M : Model H hg hβ hβ₁ b u₀ Ω ι)

def Model.path : Ω → Space H := NativeContinuousPath.path H M.W M.continuous

theorem Model.path_measurable : Measurable M.path :=
  NativeContinuousPath.measurable_path H M.W M.continuous
    (M.predictable.mono (predictable_le_product M.F)).measurable

theorem Model.adapted : StronglyAdapted M.F M.W := by
  exact IsStronglyPredictable.stronglyAdapted M.predictable

theorem Model.moment :
    Integrable (fun p : ℝ≥0×Ω => ‖M.W p.1 p.2‖^2) (energyMeasure M.μ H) := by
  obtain ⟨R,hR,hb⟩ := ScalarStoppedMomentUniform.bound (H := H) hg hβ hβ₁ b u₀
  have he := hb M.F M.μ M.W M.predictable M.continuous
    (FiniteCylindricalIto.terminalIto M.P.toCoordinates M.basis) _ M.equation
    (fun _ => measurable_const) (fun _ _ => by norm_num)
  exact ScalarStoppedMomentUniform.integrable_sq M.F M.μ H M.W M.predictable
    (lt_of_le_of_lt he ENNReal.ofReal_lt_top)

local notation "νM" => FiniteScalarIto.inputMeasure M.F M.μ H
local notation "G" => ScalarStatePathFiltration.filtration H

variable (ρ : Measure (Space H)) [IsProbabilityMeasure ρ] (hρ : M.μ.map M.path=ρ)

def Model.pull :
    Lp Noise 2 (FiniteScalarIto.inputMeasure G ρ H) →ₗᵢ[ℝ] Lp Noise 2 νM := by
  have hp := ScalarStatePathFiltration.preserving M.F H M.W M.continuous M.μ ρ M.adapted
    (M.predictable.mono (predictable_le_product M.F)).measurable hρ
  let _ : MeasurableSpace (ℝ≥0×Ω) := M.F.predictable
  let _ : MeasurableSpace (ℝ≥0×Space H) := (G).predictable
  exact Lp.compMeasurePreservingₗᵢ ℝ (ScalarStatePathFiltration.pull H M.W M.continuous) hp

theorem Model.pull_ae (v : Lp Noise 2 (FiniteScalarIto.inputMeasure G ρ H)) :
    M.pull ρ hρ v =ᵐ[νM] fun p => v (p.1,M.path p.2) := by
  have hp := ScalarStatePathFiltration.preserving M.F H M.W M.continuous M.μ ρ M.adapted
    (M.predictable.mono (predictable_le_product M.F)).measurable hρ
  let _ : MeasurableSpace (ℝ≥0×Ω) := M.F.predictable
  let _ : MeasurableSpace (ℝ≥0×Space H) := (G).predictable
  exact Lp.coeFn_compMeasurePreserving v hp

include hρ in
theorem Model.pull_eventually {p : ℝ≥0×Space H → Prop}
    (h : ∀ᵐ x ∂FiniteScalarIto.inputMeasure G ρ H,p x) :
    ∀ᵐ x ∂νM,p (x.1,M.path x.2) := by
  have hp := ScalarStatePathFiltration.preserving M.F H M.W M.continuous M.μ ρ M.adapted
    (M.predictable.mono (predictable_le_product M.F)).measurable hρ
  let _ : MeasurableSpace (ℝ≥0×Ω) := M.F.predictable
  let _ : MeasurableSpace (ℝ≥0×Space H) := (G).predictable
  exact hp.quasiMeasurePreserving.ae h

include hρ in
omit [IsProbabilityMeasure ρ] in
theorem Model.canonical_moment :
    Integrable (fun p : ℝ≥0×Space H => ‖state H p.1 p.2‖^2) (energyMeasure ρ H) := by
  have hp : MeasurePreserving (ScalarStatePathFiltration.pull H M.W M.continuous)
      (energyMeasure M.μ H) (energyMeasure ρ H) :=
    (MeasurePreserving.id (PredictableL2.timeMeasure H)).prod ⟨M.path_measurable,hρ⟩
  have hm : AEStronglyMeasurable (fun p : ℝ≥0×Space H => ‖state H p.1 p.2‖^2) (energyMeasure ρ H) :=
    (((ScalarStatePathFiltration.predictable H).mono (predictable_le_product G)).norm.pow 2).aestronglyMeasurable
  apply (hp.integrable_comp hm).mp
  apply M.moment.congr
  have ht := (Measure.quasiMeasurePreserving_fst (μ := PredictableL2.timeMeasure H) (ν := M.μ)).ae (timeMeasure_ae_mem H)
  filter_upwards [ht] with p hpt
  exact congrArg (fun x : RealL2 => ‖x‖^2)
    (state_path H M.W M.continuous p.1 hpt.2 p.2).symm

end SHEStochastic.ScalarCanonicalObservation
