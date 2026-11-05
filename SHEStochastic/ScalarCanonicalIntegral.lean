module

public import SHEStochastic.ScalarCanonicalCellTest
public import SHEStochastic.ScalarCanonicalDensityLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarCanonicalIntegral
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarCanonicalObservation ScalarStatePathFiltration ScalarFourierPredictableSpan
open scoped NNReal ENNReal Topology

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

variable {H : ℝ≥0} {g : ℝ → ℝ} {C β : ℝ≥0} {hg : HolderWith C β g} {hβ : 0<β} {hβ₁ : β≤1}
  {b : ScalarLinearGrowthDriftField.Data H} {u₀ : RealL2}

local notation "G" => ScalarStatePathFiltration.filtration H

variable (ρ : Measure (Space H)) [IsProbabilityMeasure ρ]
local notation "L" => Lp Noise 2 (FiniteScalarIto.inputMeasure G ρ H)

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (M : Model H hg hβ hβ₁ b u₀ Ω ι) (hM : M.μ.map M.path=ρ)

def observe : L →ₗᵢ[ℝ] Lp ℝ 2 M.μ :=
  (FiniteCylindricalIto.rawIntegral M.P.toCoordinates M.basis).comp (M.pull ρ hM)

variable {Ξ κ : Type*} [MeasurableSpace Ξ] [Countable κ] [DecidableEq κ]
  (N : Model H hg hβ hβ₁ b u₀ Ξ κ) (hN : N.μ.map N.path=ρ)

private def common : Submodule ℝ L where
  carrier := {v | ∃ f : Space H→ℝ,Measurable f ∧
    observe ρ M hM v =ᵐ[M.μ] f ∘ M.path ∧ observe ρ N hN v =ᵐ[N.μ] f ∘ N.path}
  zero_mem' := by
    refine ⟨fun _ => 0,measurable_const,?_,?_⟩ <;> rw [map_zero] <;>
      exact Lp.coeFn_zero ℝ 2 _
  add_mem' := by
    intro a d ha hd
    obtain ⟨f,hf,hMf,hNf⟩ := ha
    obtain ⟨k,hk,hMk,hNk⟩ := hd
    refine ⟨fun z => f z+k z,hf.add hk,?_,?_⟩ <;> rw [map_add]
    · filter_upwards [Lp.coeFn_add (observe ρ M hM a) (observe ρ M hM d),hMf,hMk]
        with ω h₁ h₂ h₃
      rw [h₁,Pi.add_apply,h₂,h₃]
      rfl
    · filter_upwards [Lp.coeFn_add (observe ρ N hN a) (observe ρ N hN d),hNf,hNk]
        with ω h₁ h₂ h₃
      rw [h₁,Pi.add_apply,h₂,h₃]
      rfl
  smul_mem' := by
    intro a v hv
    obtain ⟨f,hf,hMf,hNf⟩ := hv
    refine ⟨fun z => a*f z,hf.const_mul a,?_,?_⟩ <;> rw [map_smul]
    · filter_upwards [Lp.coeFn_smul a (observe ρ M hM v),hMf] with ω h₁ h₂
      rw [h₁,Pi.smul_apply,h₂]
      rfl
    · filter_upwards [Lp.coeFn_smul a (observe ρ N hN v),hNf] with ω h₁ h₂
      rw [h₁,Pi.smul_apply,h₂]
      rfl

/-- A predictable direction defined on a common drift-free state law
has one Borel terminal integral on that path space in both realizations. -/
theorem exists_common (h₀ : ∀ x,g x≠0) (v : L) :
    ∃ j : Space H→ℝ,Measurable j ∧ (j ∘ M.path) =ᵐ[M.μ] observe ρ M hM v ∧
      (j ∘ N.path) =ᵐ[N.μ] observe ρ N hN v := by
  let hI := M.canonical_moment ρ hM
  let gen := generator G ρ H (state H) (ScalarStatePathFiltration.predictable H) hg hβ hβ₁ hI
  let V := Submodule.span ℝ (range gen)
  have hV : V≤common ρ M hM N hN := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨ScalarCanonicalCellTest.test H i,ScalarCanonicalCellTest.test_measurable H i,
      ScalarCanonicalCellTest.integral_test M ρ hM hI i,ScalarCanonicalCellTest.integral_test N ρ hN hI i⟩
  have hd : V.topologicalClosure=⊤ :=
    dense_span G ρ H (state H) (ScalarStatePathFiltration.predictable H) hg hβ hβ₁ hI h₀
  have hvc : v∈closure (V : Set L) := by
    change v∈V.topologicalClosure
    rw [hd]
    exact Submodule.mem_top
  obtain ⟨a,ha,halim⟩ := mem_closure_iff_seq_limit.mp hvc
  have hrep (k : ℕ) : ∃ f : Space H→ℝ, Measurable f ∧
      observe ρ M hM (a k) =ᵐ[M.μ] f ∘ M.path ∧
      observe ρ N hN (a k) =ᵐ[N.μ] f ∘ N.path := hV (ha k)
  choose f hf hFM hFN using hrep
  have hLM := tendstoInMeasure_of_tendsto_Lp (((observe ρ M hM).continuous.tendsto v).comp halim)
  have hLN := tendstoInMeasure_of_tendsto_Lp (((observe ρ N hN).continuous.tendsto v).comp halim)
  obtain ⟨j,hj,hJM,hJN⟩ := ScalarCanonicalDensityLimit.exists_common_limit (Ξ := Ξ) (ν := N.μ)
    M.path_measurable f hf (observe ρ M hM v) (TendstoInMeasure.congr_left hFM hLM)
  exact ⟨j,hj,hJM,hJN N.path N.path_measurable (hN.trans hM.symm) _
    (TendstoInMeasure.congr_left hFN hLN)⟩

end SHEStochastic.ScalarCanonicalIntegral
