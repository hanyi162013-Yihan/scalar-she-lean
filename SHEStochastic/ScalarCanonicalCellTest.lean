module

public import SHEStochastic.ScalarCanonicalObservation
public import SHEStochastic.FiniteItoStoppedVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarCanonicalCellTest
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarStatePathFiltration ScalarCanonicalObservation ScalarFourierPredictableSpan
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

variable (H : ℝ≥0)
local notation "G" => ScalarStatePathFiltration.filtration H
local notation "φ" => NativeFourierHeatCoordinate.coordinate

def mode (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (z : Space H) : ℝ :=
  Real.exp ((min t H : ℝ≥0)*(n : ℝ)^2)*φ ψ n (state H t z)

def test (i : Index G) : Space H → ℝ :=
  i.2.2.event.indicator (fun z => mode H i.1 i.2.1 i.2.2.right z-mode H i.1 i.2.1 i.2.2.left z)

theorem mode_measurable (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) : Measurable (mode H ψ n t) :=
  ((φ ψ n).continuous.measurable.comp ((adapted H t).mono ((G).le t) le_rfl)).const_mul _

theorem test_measurable (i : Index G) : Measurable (test H i) :=
  ((mode_measurable H i.1 i.2.1 i.2.2.right).sub
    (mode_measurable H i.1 i.2.1 i.2.2.left)).indicator ((G).le _ _ i.2.2.past)

variable {H} {g : ℝ → ℝ} {C β : ℝ≥0} {hg : HolderWith C β g} {hβ : 0<β} {hβ₁ : β≤1}
  {b : ScalarLinearGrowthDriftField.Data H} {u₀ : RealL2}
  {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (M : Model H hg hβ hβ₁ b u₀ Ω ι)

local notation "νM" => FiniteScalarIto.inputMeasure M.F M.μ H
local notation "J" => FiniteCylindricalIto.terminalIto M.P.toCoordinates M.basis

theorem input_time_le : ∀ᵐ p : ℝ≥0×Ω ∂νM,p.1≤H := by
  let _ : MeasurableSpace (ℝ≥0×Ω) := M.F.predictable
  let S : Set (ℝ≥0×Ω) := {p | (p.1 : ℝ)≤(H : ℝ)}
  have hs : MeasurableSet[M.F.predictable] S :=
    measurableSet_le (PredictableClock.real_time_measurable M.F) measurable_const
  change ∀ᵐ p ∂νM,p∈S
  rw [ae_iff]
  change (νM) Sᶜ=0
  rw [NativeRowRepresentatives.inputMeasure_eq,trim_measurableSet_eq _ hs.compl]
  have ht := (Measure.quasiMeasurePreserving_fst (μ := PredictableL2.timeMeasure H) (ν := M.μ)).ae (timeMeasure_ae_mem H)
  exact (ae_iff.mp (ht.mono fun p hp => show p∈S from by exact_mod_cast hp.2))

private theorem mode_integral (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    (J).integral (StoppedItoInputs.stop M.F M.μ H t
      (ScalarGrowingFourierInput.input M.F M.μ H M.W M.predictable hg hβ hβ₁ ψ n M.moment)) =ᵐ[M.μ]
        fun ω => mode H ψ n t (M.path ω)-φ ψ n u₀ := by
  let v := ScalarGrowingFourierInput.input M.F M.μ H M.W M.predictable hg hβ hβ₁ ψ n M.moment
  have h := ScalarGrowingFourierInput.increment_primitive M.F M.μ H M.W M.predictable hg hβ hβ₁ ψ n
    M.P M.basis M.continuous M.nulls b u₀ M.equation M.moment (min t H) (min_le_right _ _)
  have hv : StoppedItoInputs.stop M.F M.μ H t v =
      StoppedItoInputs.stop M.F M.μ H (min t H) v := by
    nth_rewrite 1 [←FiniteItoStoppedVersions.stop_horizon v]
    rw [StoppedInputAlgebra.stop_stop]
  rw [show _ = StoppedItoInputs.stop M.F M.μ H t v from rfl,hv]
  refine h.mono fun ω hω => hω.trans ?_
  have hs : state H t (M.path ω)=M.W (min t H) ω := by
    change M.W (min (t : ℝ) (H : ℝ)).toNNReal ω=_
    rw [←NNReal.coe_min,Real.toNNReal_coe]
  unfold mode
  dsimp only
  rw [hs]

variable (ρ : Measure (Space H)) [IsProbabilityMeasure ρ] (hρ : M.μ.map M.path=ρ)
  (hM : Integrable (fun p : ℝ≥0×Space H => ‖state H p.1 p.2‖^2) (energyMeasure ρ H))

local notation "gen" => generator G ρ H (state H) (ScalarStatePathFiltration.predictable H) hg hβ hβ₁ hM

/-- A common state-path test gives the exact stochastic integral of
each predictable Fourier generator under every realization. -/
theorem integral_test (i : Index G) :
    FiniteCylindricalIto.rawIntegral M.P.toCoordinates M.basis (M.pull ρ hρ (gen i)) =ᵐ[M.μ]
      fun ω => test H i (M.path ω) := by
  classical
  let c := i.2.2
  let Z (ω : Ω) : ℝ := c.event.indicator (fun _ => 1) (M.path ω)
  have hA : MeasurableSet[M.F c.left] (M.path ⁻¹' c.event) :=
    ScalarStatePathFiltration.path_past M.F H M.W M.continuous M.adapted c.left c.past
  have hZ : StronglyMeasurable[M.F c.left] Z := by
    apply Measurable.stronglyMeasurable
    change Measurable[M.F c.left] ((M.path ⁻¹' c.event).indicator (fun _ => (1 : ℝ)))
    exact measurable_const.indicator hA
  have hZb (ω : Ω) : |Z ω|≤1 := by
    by_cases h : M.path ω∈c.event <;> simp [Z,h]
  let u := ScalarGrowingFourierInput.input M.F M.μ H M.W M.predictable hg hβ hβ₁ i.1 i.2.1 M.moment
  obtain ⟨v,hv,hIv⟩ := PredictableMultiplier.cell J (FiniteCylindricalIto.pastLocality M.P M.basis)
    u c.left c.right c.ordered Z hZ 1 zero_le_one hZb
  have hv' := NativeRowRepresentatives.transport_ae v _
    ((PredictableSteps.step_stronglyMeasurable M.F c.left c.right hZ).smul (Lp.stronglyMeasurable u)) hv
  have hu := FiniteCylindricalIto.processTransport_ae u
  have hur := row_ae M.F M.μ H M.W M.predictable hg hβ hβ₁ M.moment i.1 i.2.1
  have hrc := row_ae G ρ H (state H) (ScalarStatePathFiltration.predictable H) hg hβ hβ₁ hM i.1 i.2.1
  have hc := cell_ae G ρ H
    (row G ρ H (state H) (ScalarStatePathFiltration.predictable H) hg hβ hβ₁ hM i.1 i.2.1) c
  have hLift : M.pull ρ hρ (gen i)=FiniteCylindricalIto.processTransport v := by
    apply Lp.ext
    filter_upwards [M.pull_ae ρ hρ (gen i),M.pull_eventually ρ hρ hc,M.pull_eventually ρ hρ hrc,
      hv',hu,hur,input_time_le M] with p hl hc hr hv hu hur ht
    change M.pull ρ hρ (gen i) p=_
    rw [hl]
    change (gen i) (p.1,M.path p.2)=_
    change (gen i) (p.1,M.path p.2) = _ at hc
    change FiniteCylindricalIto.processTransport v p = PredictableSteps.step c.left c.right Z p • u p at hv
    change FiniteCylindricalIto.processTransport u p = _ at hur
    rw [hc,hv,←hu,hur]
    have he : ScalarGrowingFourierInput.row H (state H) hg hβ hβ₁ i.1 i.2.1 (p.1,M.path p.2)=
        ScalarGrowingFourierInput.row H M.W hg hβ hβ₁ i.1 i.2.1 p := by
      have hState : state H p.1 (M.path p.2)=M.W p.1 p.2 :=
        state_path H M.W M.continuous p.1 ht p.2
      simp only [ScalarGrowingFourierInput.row,FourierHeatInput.multiplier,UnboundedNativeHeatEquation.physical]
      rw [hState]
    by_cases h : p.1∈Ioc c.left c.right <;> by_cases hA : M.path p.2∈c.event <;>
      simp [Cell.region,h,hA,hr,he,PredictableSteps.step,Z]
  rw [hLift]
  change (J).integral v =ᵐ[M.μ] _
  filter_upwards [hIv,mode_integral M i.1 i.2.1 c.left,mode_integral M i.1 i.2.1 c.right]
    with ω hIv hl hr
  rw [hIv,hl,hr]
  have hh : mode H i.1 i.2.1 c.right (M.path ω)-φ i.1 i.2.1 u₀-
      (mode H i.1 i.2.1 c.left (M.path ω)-φ i.1 i.2.1 u₀) =
      mode H i.1 i.2.1 c.right (M.path ω)-mode H i.1 i.2.1 c.left (M.path ω) := by ring
  rw [hh]
  by_cases h : M.path ω∈c.event <;> simp [test,c,Z,h]

end SHEStochastic.ScalarCanonicalCellTest
