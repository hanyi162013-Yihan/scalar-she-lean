module

public import SHEStochastic.MatrixUnboundedCompletedLocalField
public import SHEStochastic.NativeRemainderObservation
public import SHEStochastic.L2EuclideanCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixUnboundedContinuousConvolution
open MeasureTheory SHE MatrixInfiniteHaar HeatParameterCover HeatParameterCoordinates HeatParameterPullback
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  MatrixUnboundedCompletedGlobal.completedSigma S
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- Choose the already proved continuous stochastic heat field for every
finite vector component. -/
def rowField (H : ℝ≥0) (i : Fin n) :
    Parameter → RandomInitialBrownianFamily.Space ρ S.law.toMeasure → ℝ :=
  Classical.choose (MatrixUnboundedCompletedLocalField.exists_row_field S H i)

theorem rowField_measurable (H : ℝ≥0) (i : Fin n) (p : Parameter) :
    Measurable (rowField S H i p) := by
  obtain ⟨hm,_,_,_,_⟩ := Classical.choose_spec
    (MatrixUnboundedCompletedLocalField.exists_row_field S H i)
  exact hm p

theorem rowField_adapted (H : ℝ≥0) (i : Fin n) (p : Parameter) :
    StronglyMeasurable[(RandomInitialBrownianFamily.filtration
      (Measure.dirac () : Measure Unit) S.law.toMeasure
      (MatrixBlockNaturalFiltration.filtration 1)) (GlobalHeatParameter.time H p)]
      (rowField S H i p) := by
  obtain ⟨_,ha,_,_,_⟩ := Classical.choose_spec
    (MatrixUnboundedCompletedLocalField.exists_row_field S H i)
  exact ha p

theorem rowField_local (H : ℝ≥0) (i : Fin n) (N : ℕ) (p : Parameter) :
    ∀ᵐ ω ∂μc,
      (GlobalHeatParameter.time H p : WithTop ℝ≥0) <
        ContinuousNormExit.exit
          (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N ω →
      rowField S H i p ω = UnboundedGlobalLocalVersion.observation
        (RandomInitialBrownianFamily.filtration
          (Measure.dirac () : Measure Unit) S.law.toMeasure
          (MatrixBlockNaturalFiltration.filtration 1))
        (MatrixUnboundedCompletedLocalField.nativeState S)
        (MatrixUnboundedCompletedLocalField.native_predictable S)
        (MatrixDiffusionRows.holder hG i) hβ hβ1 μc H
        (MatrixUnboundedCompletedGlobal.family S H) (VectorNativeHaarBasis.basis (n := n)) N p ω := by
  obtain ⟨_,_,_,hl,_⟩ := Classical.choose_spec
    (MatrixUnboundedCompletedLocalField.exists_row_field S H i)
  exact hl N p

theorem rowField_continuous (H : ℝ≥0) (i : Fin n)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Continuous (fun p => rowField S H i p ω) := by
  obtain ⟨_,_,hc,_,_⟩ := Classical.choose_spec
    (MatrixUnboundedCompletedLocalField.exists_row_field S H i)
  exact hc ω

/-- One scalar component of the local stochastic convolution. -/
def scalarRemainder (H : ℝ≥0) (i : Fin n) (t : ShortTime)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    SHE.DyadicApproximation.RealL2 :=
  NativeRemainderObservation.remainder
    ⟨fun p => rowField S H i p ω, rowField_continuous S H i ω⟩ t

theorem scalar_continuous (H : ℝ≥0) (i : Fin n)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Continuous (fun t => scalarRemainder S H i t ω) :=
  NativeRemainderObservation.continuous_remainder _

/-- Assemble all scalar row convolutions into the paper's genuine
unit-circle vector L2 space. -/
def physical (H : ℝ≥0) (t : ShortTime)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) : Physical (d := Fin n) :=
  (L2EuclideanCoordinates.equivalence ν).symm
    (WithLp.toLp 2 (fun i : Fin n => scalarRemainder S H i t ω))

theorem component (H : ℝ≥0) (t : ShortTime)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) (i : Fin n) :
    L2EuclideanCoordinates.coordinates ν (physical S H t ω) i =
      scalarRemainder S H i t ω := by
  change ((L2EuclideanCoordinates.equivalence ν)
    ((L2EuclideanCoordinates.equivalence ν).symm
      (WithLp.toLp 2 (fun i : Fin n => scalarRemainder S H i t ω)))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- Positive-heat observations of the assembled vector remainder are
exactly the heat averages of the selected original matrix-row fields. -/
theorem smoothed_component (H : ℝ≥0) (t : ShortTime)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) (i : Fin n)
    {ε : ℝ} (hε : 0<ε) (x : SHE.StoppedFourier.HeatCircle) :
    NativeHeatObservation.functional ε x
      (L2EuclideanCoordinates.coordinates ν (physical S H t ω) i) =
      ∫ a : SHE.StoppedFourier.HeatCircle,
        rowField S H i (point t a) ω ∂PhysicalHeatKernelMeasure.measure ε hε x := by
  rw [component]
  exact NativeRemainderObservation.observation hε x
    ⟨fun p => rowField S H i p ω, rowField_continuous S H i ω⟩ t

theorem continuous_paths (H : ℝ≥0)
    (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Continuous (fun t : ShortTime => physical S H t ω) := by
  have hrow : Continuous (fun t : ShortTime =>
      fun i : Fin n => scalarRemainder S H i t ω) :=
    continuous_pi (fun i => scalar_continuous S H i ω)
  have hpi : Continuous (fun t : ShortTime =>
      WithLp.toLp 2 (fun i : Fin n => scalarRemainder S H i t ω)) :=
    (PiLp.continuous_toLp 2 _).comp hrow
  exact (L2EuclideanCoordinates.equivalence ν).symm.continuous.comp hpi

end SHEStochastic.MatrixUnboundedContinuousConvolution
