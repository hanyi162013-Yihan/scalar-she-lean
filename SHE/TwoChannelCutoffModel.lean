module

public import SHE.NonlinearTwoChannelStep
public import SHE.CutoffWordAnalytic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.TwoChannelCutoffModel
open MeasureTheory Set PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
open NativeHeatObservation NativeObservationNaturality WordRecursion CutoffWordLevel CutoffWordAnalytic
open IntegratedPhysicalStep OrthogonalItoChannels
open scoped NNReal ENNReal
local instance twoChannelCutoffModel_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance twoChannelCutoffModel_realSigma : MeasurableSpace RealL2 := borel _
local instance twoChannelCutoffModel_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance twoChannelCutoffModel_nativeSigma : MeasurableSpace StoppedFourier.CircleL2 := borel _
local instance twoChannelCutoffModel_nativeBorel : BorelSpace StoppedFourier.CircleL2 := ⟨rfl⟩
local instance twoChannelCutoffModel_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance twoChannelCutoffModel_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance twoChannelCutoffModel_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance twoChannelCutoffModel_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Explicit native mild data with separate common additive and residual
noises. The scalar direct-sum integral retains both channels. Native
clock conversion and the mild equation are visible model fields. -/
structure Model (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
    (κ : ℝ) (a : ℝ → ℝ) (ell M : ℝ) where
  additive_pos : 0 < κ
  lower_pos : 0 < ell
  variance_measurable : Measurable a
  variance_bounds : ∀ z,ell ≤ a z ∧ a z ≤ M
  coefficient : ℝ≥0 × Ω → EllipticField ell M
  coefficient_predictable : StronglyMeasurable[𝓕.predictable] coefficient
  state : ℝ≥0 × Ω → RealL2
  state_predictable : StronglyMeasurable[𝓕.predictable] state
  state_continuous : ∀ ω,Continuous (fun t => state (t,ω))
  null_complete : NullCompleteFiltration.ContainsNullSets 𝓕 μ
  additiveIto : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h
  residualIto : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h
  scalarIto : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h
  additive_naturality : StandardScalarNaturality additiveIto (leftIntegral 𝓕 μ h scalarIto)
  residual_naturality : StandardScalarNaturality residualIto (rightIntegral 𝓕 μ h scalarIto)
  finiteIto : StandardFiniteIto.Universal 𝓕 μ h scalarIto
  initial : RealL2
  additiveInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  residualInput : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h
  additive_kernel : ∀ t : ℝ≥0,t ≤ h → additiveInput t=ᵐ[energyMeasure μ h]
    (fun p => NativeHeatObservation.kernel κ κ additive_pos
      ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ additive_pos))
  residual_kernel : ∀ t : ℝ≥0,t ≤ h → residualInput t=ᵐ[energyMeasure μ h]
    (fun p => NativeHeatObservation.kernel ell M lower_pos ((t:ℝ)-(p.1:ℝ),coefficient p))
  mild_identity : ∀ t : ℝ≥0,t ≤ h → ∀ᵐ ω ∂μ,
    state (t,ω)=NativeHeatObservation.heat (t:ℝ) initial+
      additiveIto.integral (additiveInput t) ω+residualIto.integral (residualInput t) ω
  coefficient_identity : ∀ p : ℝ≥0 × Ω,(coefficient p).1=CoefficientFields.coefficient a variance_measurable M
    (NonlinearHaarIntegrand.absBound lower_pos variance_bounds) (state p)

namespace Model
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {h : ℝ≥0} {κ : ℝ} {a : ℝ → ℝ} {ell M : ℝ} (m : Model 𝓕 μ h κ a ell M)

def physicalState (p : Ω × ℝ) : StoppedFourier.CircleL2 := embed (m.state (p.2.toNNReal,p.1))
def physicalField (p : Ω × (ℝ × HeatCircle)) : ℝ := PredictableScalarField.wordField m.state p.1 p.2

theorem physicalState_measurable : Measurable m.physicalState := by
  have hU : Measurable m.state := (m.state_predictable.mono (PredictableL2.predictable_le_product 𝓕)).measurable
  have hp : Measurable (fun p : Ω × ℝ => (p.2.toNNReal,p.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  exact embed.continuous.measurable.comp (hU.comp hp)

theorem physicalField_measurable : Measurable m.physicalField :=
  PredictableScalarField.wordField_measurable 𝓕 m.state_predictable

/-- Every positive-gap variable word level receives its actual centered
Itô term from the two original noise channels. No wordwise stochastic
applicability, bracket, or centering premise is supplied. -/
theorem exists_level_ito {P : Type*} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
    (L : Level R P n) (hA : R.totalVariance=(fun z => κ+a z)) (hh : R.horizon ≤ (h:ℝ))
    {ε : ℝ} (hε : 0 < ε) (hgap : ∀ p i,ε ≤ (L.observations.observations p i).target-L.terminal p) :
    ∃ N : P → (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ,
      ItoConditions (physicalLevel L m.physicalState m.physicalField N) μ := by
  have hex (p : P) : ∃ N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ,
      (∀ G,Integrable (N G) μ ∧ (∫ ω,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω => observe (fun t => m.physicalState (ω,t)) (fun q => m.physicalField (ω,q))
          (L.observations.observations p))
        (fun ω t => CovarianceMatrix.densityMatrix (fun q => κ+a (m.physicalField (ω,q)))
          (L.observations.observations p) t) R.base (L.terminal p) N := by
    let b : ℝ≥0 := (L.terminal p).toNNReal
    have hb0 : 0 ≤ L.terminal p := R.base_nonneg.trans (L.terminal_base p)
    have hbcoe : (b:ℝ)=L.terminal p := Real.coe_toNNReal _ hb0
    have hbh : b ≤ h := by
      exact_mod_cast (show (b:ℝ) ≤ h by rw [hbcoe]; exact (L.terminal_horizon p).trans hh)
    have hgapb : ∀ i,ε ≤ (L.observations.observations p i).target-(b:ℝ) := by
      simpa only [hbcoe] using hgap p
    have horder : R.base ≤ (b:ℝ) := by rw [hbcoe]; exact L.terminal_base p
    have hi := NonlinearTwoChannelStep.finiteItoInput 𝓕 μ h κ m.additive_pos m.lower_pos
      m.coefficient m.coefficient_predictable m.state m.state_predictable a m.variance_measurable
      m.variance_bounds m.coefficient_identity m.null_complete m.additiveIto m.residualIto m.scalarIto
      m.additive_naturality m.residual_naturality m.finiteIto m.initial m.state_continuous
      m.additiveInput m.residualInput m.additive_kernel m.residual_kernel m.mild_identity
      (L.observations.observations p) b hbh hε hgapb R.base_nonneg horder
    rw [hbcoe] at hi
    convert hi using 1
    rfl
  choose N hN using hex
  refine ⟨N,?_,?_,?_⟩
  · intro p
    exact Filter.Eventually.of_forall
      (PredictableScalarField.wordField_section_measurable 𝓕 m.state_predictable)
  · intro p
    simpa only [physicalLevel,Level.window,hA] using (hN p).2
  · intro p
    exact ((hN p).1 _).2

end Model
end SHE.TwoChannelCutoffModel
