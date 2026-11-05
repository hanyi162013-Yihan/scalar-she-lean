module

public import SHEStochastic.ScalarCanonicalIntegral
public import SHEStochastic.ScalarDriftNativeDirection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarCanonicalLikelihood
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

variable {H : ℝ≥0} {g : ℝ → ℝ} {C β : ℝ≥0} {hg : HolderWith C β g} {hβ : 0<β} {hβ₁ : β≤1}
  {b : ScalarLinearGrowthDriftField.Data H} {u₀ : RealL2}

local notation "G" => ScalarStatePathFiltration.filtration H
local notation "raw" m:max => Lp Noise 2 (FiniteScalarIto.inputMeasure (Model.F m) (Model.μ m) H)
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

variable (θ : ScalarLinearGrowthDriftField.Data H)

def energy (z : Space H) : ℝ :=
  ∫ t,‖ScalarDriftNativeDirection.row θ (Function.uncurry (state H)) (t,z)‖^2 ∂νt

theorem energy_measurable : Measurable (energy θ) := by
  have hm := (((ScalarDriftNativeDirection.predictable G θ (Function.uncurry (state H))
    (ScalarStatePathFiltration.predictable H)).mono (predictable_le_product G)).norm.pow 2)
  exact hm.integral_prod_left'.measurable

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (M : Model H hg hβ hβ₁ b u₀ Ω ι)
  (ρ : Measure (Space H)) [IsProbabilityMeasure ρ] (hM : M.μ.map M.path=ρ)

private theorem pull_control (v : Lp Noise 2 (FiniteScalarIto.inputMeasure G ρ H))
    (hv : v =ᵐ[FiniteScalarIto.inputMeasure G ρ H]
      ScalarDriftNativeDirection.row θ (Function.uncurry (state H))) :
    M.pull ρ hM v =ᵐ[FiniteScalarIto.inputMeasure M.F M.μ H]
      ScalarDriftNativeDirection.row θ (Function.uncurry M.W) := by
  filter_upwards [M.pull_ae ρ hM v,M.pull_eventually ρ hM hv,ScalarCanonicalCellTest.input_time_le M]
    with p hp hv ht
  rw [hp,hv]
  have he : state H p.1 (M.path p.2)=M.W p.1 p.2 :=
    state_path H M.W M.continuous p.1 ht p.2
  change NativePhysicalState.push (ScalarLinearGrowthDriftField.field θ
      (p.1,state H p.1 (M.path p.2))) =
    NativePhysicalState.push (ScalarLinearGrowthDriftField.field θ (p.1,M.W p.1 p.2))
  rw [he]

private theorem energy_eq (w : raw M)
    (hw : w =ᵐ[FiniteScalarIto.inputMeasure M.F M.μ H]
      ScalarDriftNativeDirection.row θ (Function.uncurry M.W)) :
    NativeEnergy.energy w =ᵐ[M.μ] energy θ ∘ M.path := by
  filter_upwards [NativeEnergy.energy_ae_of_ae w _ hw] with ω hω
  change _=energy θ (M.path ω)
  rw [hω,energy,←SHEStochastic.timeMeasure_eq]
  apply integral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with t ht
  have he : state H t (M.path ω)=M.W t ω :=
    state_path H M.W M.continuous t ht.2 ω
  change ‖NativePhysicalState.push (ScalarLinearGrowthDriftField.field θ (t,M.W t ω))‖^2=
    ‖NativePhysicalState.push (ScalarLinearGrowthDriftField.field θ (t,state H t (M.path ω)))‖^2
  rw [he]

variable {Ξ κ : Type*} [MeasurableSpace Ξ] [Countable κ] [DecidableEq κ]
  (N : Model H hg hβ hβ₁ b u₀ Ξ κ) (hN : N.μ.map N.path=ρ)

include hM hN in
/-- The positive reverse likelihood is a common Borel function of
the drift-free state path. It is recovered from the actual control
and its stochastic integral, including the exact half energy. -/
theorem exists_common (h₀ : ∀ x,g x≠0) :
    ∃ (w : raw M) (w' : raw N) (D : Space H → ℝ≥0∞),
      w =ᵐ[FiniteScalarIto.inputMeasure M.F M.μ H]
        ScalarDriftNativeDirection.row θ (Function.uncurry M.W) ∧
      w' =ᵐ[FiniteScalarIto.inputMeasure N.F N.μ H]
        ScalarDriftNativeDirection.row θ (Function.uncurry N.W) ∧
      Measurable D ∧
      (fun ω => ENNReal.ofReal (NativeExponential.density M.P M.basis 1 w ω)) =ᵐ[M.μ] D ∘ M.path ∧
      (fun ω => ENNReal.ofReal (NativeExponential.density N.P N.basis 1 w' ω)) =ᵐ[N.μ] D ∘ N.path := by
  obtain ⟨v,hv,_⟩ := ScalarDriftNativeDirection.exists_control G ρ θ (Function.uncurry (state H))
    (ScalarStatePathFiltration.predictable H) (M.canonical_moment ρ hM)
  let w := M.pull ρ hM v
  let w' := N.pull ρ hN v
  have hw := pull_control θ M ρ hM v hv
  have hw' := pull_control θ N ρ hN v hv
  obtain ⟨j,hj,hJM,hJN⟩ := ScalarCanonicalIntegral.exists_common ρ M hM N hN h₀ v
  let D (z : Space H) := ENNReal.ofReal (Real.exp (j z-energy θ z/2))
  refine ⟨w,w',D,hw,hw',((hj.sub ((energy_measurable θ).div_const 2)).exp).ennreal_ofReal,?_,?_⟩
  · filter_upwards [hJM,energy_eq θ M w hw] with ω hJ hE
    change j (M.path ω)=FiniteCylindricalIto.rawIntegral M.P.toCoordinates M.basis w ω at hJ
    change NativeEnergy.energy w ω=energy θ (M.path ω) at hE
    simp only [NativeExponential.density,one_mul,one_pow,hE,D,Function.comp_apply,hJ]
  · filter_upwards [hJN,energy_eq θ N w' hw'] with ω hJ hE
    change j (N.path ω)=FiniteCylindricalIto.rawIntegral N.P.toCoordinates N.basis w' ω at hJ
    change NativeEnergy.energy w' ω=energy θ (N.path ω) at hE
    simp only [NativeExponential.density,one_mul,one_pow,hE,D,Function.comp_apply,hJ]

end SHEStochastic.ScalarCanonicalLikelihood
