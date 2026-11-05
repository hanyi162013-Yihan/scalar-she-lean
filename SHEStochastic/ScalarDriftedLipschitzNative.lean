module

public import SHEStochastic.ScalarLipschitzLawComparison
public import SHEStochastic.NativeTimeDilatedFamily
public import SHEStochastic.CanonicalBrownianFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarDriftedLipschitzNative
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarCanonicalObservation ScalarDriftedNativeLaw
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

variable {I : Type} [Countable I] [DecidableEq I] (H : ℝ≥0) (hH : 0<H)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) (e : HilbertBasis I ℝ Noise)

include hH in
theorem exists_zero :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (M : @Model H g C 1 hg zero_lt_one le_rfl b u₀ Ω I m _ _),
      M.basis=e ∧ M.W 0=ᵐ[M.μ] fun _ => u₀ := by
  let : Encodable I := Encodable.ofCountable I
  let source := CanonicalBrownianFamily.reindex (⟨Encodable.encode,Encodable.encode_injective⟩ : I ↪ ℕ)
  let F := PredictableTimeDilation.filtration CanonicalBrownianFamily.filtration
    (PredictableTimeDilation.clock H hH)
  obtain ⟨P₀,_⟩ := NativeTimeDilatedFamily.exists_family CanonicalBrownianFamily.filtration
    CanonicalBrownianFamily.measure H hH 1 source e CanonicalBrownianFamily.contains_null
  let P : FiniteScalarIto.Family F CanonicalBrownianFamily.measure H I := by
    simpa only [mul_one] using P₀
  have hn : NullCompleteFiltration.ContainsNullSets F CanonicalBrownianFamily.measure := fun t =>
    CanonicalBrownianFamily.contains_null ((PredictableTimeDilation.clock H hH).symm t)
  obtain ⟨M,_,_,he,hi⟩ := ScalarLipschitzNativeExistence.exists_zero e P hg hH hn b u₀
  exact ⟨CanonicalBrownianFamily.Space,inferInstance,M,he,hi⟩

include hH in
/-- The original globally Lipschitz diffusion may be unbounded.
Existence and uniqueness with the linear-growth drift hold even for L²
initial data at this endpoint. -/
theorem exists_unique (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|) :
    ∃! law,ScalarDriftedNativeLaw.Realizes H hg zero_lt_one le_rfl b u₀ e law := by
  obtain ⟨Ω,m,M,hB,hInit⟩ := exists_zero H hH hg b u₀ e
  let _ : MeasurableSpace Ω := m
  obtain ⟨A⟩ := ScalarDriftedNativeLaw.exists_of_zero c hc hell M hB hInit
  refine ⟨A.μ.map (NativeContinuousPath.path H A.W A.continuous),⟨Ω,m,A,rfl⟩,?_⟩
  rintro q ⟨Ξ,mΞ,B,rfl⟩
  let _ : MeasurableSpace Ξ := mΞ
  exact ScalarDriftedNativeLaw.laws_eq c hc hell
    (ScalarLipschitzLawComparison.zero_unique H hg b u₀ e hH) B A

end SHEStochastic.ScalarDriftedLipschitzNative
