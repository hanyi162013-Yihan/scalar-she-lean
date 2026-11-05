module

public import SHEStochastic.ScalarDriftedNativeLaw
public import SHEStochastic.ScalarStoppedUnboundedBridge
public import SHEStochastic.ScalarUnboundedNativeExistence
public import SHEStochastic.UnboundedGlobalNativeUniqueness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarDriftedStrictNative
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarCanonicalObservation ScalarStatePathFiltration ScalarDriftedNativeLaw
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

variable (H : ℝ≥0) (hH : 0<H) {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g)
  (hβ : 0<β) (hβ₁ : β<1) (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
  (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)

local notation "e" => ScalarUnboundedFourierProjection.basis

include hell in
private theorem variance_bound : ∀ z,(c : ℝ)^2≤(g z)^2 := fun z =>
  (pow_le_pow_left₀ c.property (hell z) 2).trans_eq (sq_abs _)

include hH hc hell in
theorem zero_unique (R : ℝ) (hR : 0≤R)
    (hI : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀=ENNReal.ofReal R) :
    ZeroUnique H hg hβ hβ₁.le b u₀ e := by
  intro Ω Ξ _ _ M N hMb hNb _ _
  have hMe := ScalarStoppedUnboundedBridge.to_native M.F M.μ H M.W M.predictable M.continuous
    hg hβ hβ₁ M.P M.basis b u₀ hH M.nulls M.equation
  have hNe := ScalarStoppedUnboundedBridge.to_native N.F N.μ H N.W N.predictable N.continuous
    hg hβ hβ₁ N.P N.basis b u₀ hH N.nulls N.equation
  rw [hMb] at hMe
  rw [hNb] at hNe
  exact UnboundedGlobalNativeUniqueness.laws_eq M.F N.F M.μ N.μ H hH M.W N.W M.predictable N.predictable
    hg hβ hβ₁ M.P N.P e u₀ M.continuous N.continuous M.nulls N.nulls hMe hNe R hR hI
    ((c : ℝ)^2) (sq_pos_of_pos (show (0 : ℝ)<c from hc)) (variance_bound c hell)

include hH hc hell in
/-- Native scalar existence with Borel linear-growth drift for every
strictly subunit globally Hölder diffusion and every deterministic L² initial state. -/
theorem exists_solution :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      Nonempty (@Solution H g C β hg hβ hβ₁.le b u₀ (Fin 1×HaarNode) _ _ e Ω m) := by
  obtain ⟨Ω,m,F,μ,pμ,P,W,hW,hcont,hn,hi,he⟩ := ScalarUnboundedNativeExistence.exists_native H hH hg hβ hβ₁
    u₀ ((c : ℝ)^2) (sq_pos_of_pos (show (0 : ℝ)<c from hc)) (variance_bound c hell)
  let _ : MeasurableSpace Ω := m
  let _ : IsProbabilityMeasure μ := pμ
  have hEq := ScalarStoppedUnboundedBridge.of_native F μ H W hW hcont hg hβ hβ₁ P e b u₀ hH hn he
  let M : Model H hg hβ hβ₁.le b u₀ Ω (Fin 1×HaarNode) := ⟨μ,F,W,hW,hcont,hn,P,e,hEq⟩
  exact ⟨Ω,m,exists_of_zero c hc hell M rfl hi⟩

include hH hc hell in
theorem exists_unique (R : ℝ) (hR : 0≤R)
    (hI : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀=ENNReal.ofReal R) :
    ∃! law,Realizes H hg hβ hβ₁.le b u₀ e law := by
  obtain ⟨Ω,m,⟨S⟩⟩ := exists_solution H hH hg hβ hβ₁ b u₀ c hc hell
  let _ : MeasurableSpace Ω := m
  refine ⟨S.μ.map (NativeContinuousPath.path H S.W S.continuous),⟨Ω,m,S,rfl⟩,?_⟩
  rintro q ⟨Ξ,mΞ,T,rfl⟩
  let _ : MeasurableSpace Ξ := mΞ
  exact laws_eq c hc hell (zero_unique H hH hg hβ hβ₁ b u₀ c hc hell R hR hI) T S

end SHEStochastic.ScalarDriftedStrictNative
