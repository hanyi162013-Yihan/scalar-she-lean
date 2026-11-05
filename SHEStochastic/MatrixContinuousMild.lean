module

public import SHEStochastic.MatrixFixedHorizonPicard
public import SHEStochastic.MatrixContinuousConvolution
public import SHEStochastic.MatrixProfileCongruence
public import SHEStochastic.NativeMatrixEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixContinuousMild
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (G : MatrixNonlinearCoefficient.Coefficient d)

def field (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U) :
    Fields (d := d) F (NativeMatrixEquation.cap G) :=
  ⟨NativeMatrixEquation.profile F G U hU,fun _ => le_rfl,NativeMatrixEquation.profile_measurable F G U hU⟩

/-- The analytic-clock Haar mild equation with its coefficient evaluated
at the solution itself. All native inputs and spatial representatives
are constructed, rather than supplied by the solution interface. -/
def Equation (hH : (H : ℝ) ≤ 1) (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (u : Physical (d := d)) : Prop := ∀ t (ht : t ≤ H),
  (fun ω => U (t,ω)) =ᵐ[μ] fun ω => VectorAnalyticHeat.heat t u+
    MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
      (field G U hU).value (field G U hU).upper (field G U hU).measurable N t ht ω

/-- Continuous predictable forcing can be added to the constructed native
matrix convolution. This is the shared Picard-to-continuous-version argument,
including random heat initial data. -/
theorem exists_forced (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ z w, ‖G.value z-G.value w‖ ≤ L*‖z-w‖)
    (forcing : ℝ≥0 × Ω → Physical (d := d))
    (hforcing : StronglyMeasurable[F.predictable] forcing)
    (hcforcing : ∀ ω, Continuous (fun t => forcing (t,ω)))
    (z : Process (E := Physical (d := d)) F μ H)
    (hz : z =ᵐ[energyMeasure μ H] forcing) :
    ∃ (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U),
      (∀ ω, Continuous (fun t => U (t,ω))) ∧
      ∀ t (ht : t ≤ H), (fun ω => U (t,ω)) =ᵐ[μ] fun ω => forcing (t,ω)+
        MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
          (field G U hU).value (field G U hU).upper (field G U hU).measurable N t ht ω := by
  obtain ⟨v,hv,_⟩ := MatrixFixedHorizonPicard.exists_unique_forced hH N G hL hLip z
  let a := MatrixPredictableConvolution.nonlinearField G v
  let Y : ℝ≥0 × Ω → Physical (d := d) := fun p => forcing p+
    MatrixContinuousConvolution.version hH (NativeMatrixEquation.cap_nonneg G) a N p.1 p.2
  have hY : StronglyMeasurable[F.predictable] Y :=
    hforcing.add
      (MatrixContinuousConvolution.predictable hH (NativeMatrixEquation.cap_nonneg G) a N hnull hH0)
  have hc (ω : Ω) : Continuous (fun t => Y (t,ω)) := by
    exact (hcforcing ω).add
      (MatrixContinuousConvolution.continuous hH (NativeMatrixEquation.cap_nonneg G) a N hH0 ω)
  have he : (fun p => v p) =ᵐ[energyMeasure μ H] Y := by
    have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_add z
      (MatrixPredictableConvolution.map hH N G v))
    rw [← hv] at hs
    filter_upwards [hs,hz,
      MatrixContinuousConvolution.convolution_ae_version hH (NativeMatrixEquation.cap_nonneg G) a N hH0]
      with p hp hi hn
    rw [hp,Pi.add_apply,hi]
    change forcing p+MatrixPredictableConvolution.convolution hH
      (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G) N a p=Y p
    rw [hn]
  let b := field G Y hY
  have hab : ∀ᵐ p ∂energyMeasure μ H,
      (a.value p).value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] (b.value p).value := by
    filter_upwards [he] with p hp
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact MatrixProfileCongruence.nonlinear_value_ae G (fun p => v p) Y (Lp.stronglyMeasurable v) hY p hp
  refine ⟨Y,hY,hc,?_⟩
  intro t ht
  have hi := MatrixProfileCongruence.input_eq hH (NativeMatrixEquation.cap_nonneg G) a b hab t ht
  have hval : MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G)
      (NativeMatrixEquation.cap_nonneg G) a.value a.upper a.measurable N t ht=
      MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G)
      (NativeMatrixEquation.cap_nonneg G) b.value b.upper b.measurable N t ht :=
    congrArg (NativeMatrixConvolution.terminalIto N).integral hi
  filter_upwards [MatrixContinuousConvolution.version_ae_of_le hH
    (NativeMatrixEquation.cap_nonneg G) a N hH0 t ht] with ω hω
  change forcing (t,ω)+MatrixContinuousConvolution.version hH
    (NativeMatrixEquation.cap_nonneg G) a N t ω=forcing (t,ω)+_
  rw [hω,hval]

/-- Every bounded globally Lipschitz elliptic matrix coefficient has a
continuous predictable Haar mild solution on any prescribed positive
H≤1, with arbitrary deterministic vector L2 initial data. -/
theorem exists_solution (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode)) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ z w, ‖G.value z-G.value w‖ ≤ L*‖z-w‖) (u : Physical (d := d)) :
    ∃ (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U),
      (∀ ω, Continuous (fun t => U (t,ω))) ∧ Equation G hH N U hU u := by
  apply exists_forced G hH hH0 hnull N hL hLip (VectorHeatInitialProcess.function u)
    (VectorHeatInitialProcess.predictable F u) _ (VectorHeatInitialProcess.process F μ H u)
    (VectorHeatInitialProcess.process_ae F μ H u)
  intro ω
  have hi : Continuous (fun t : ℝ≥0 => ((t : ℝ)/NativeHeatObservation.timeScale,u)) :=
    (NNReal.continuous_coe.div_const _).prodMk continuous_const
  exact Continuous.comp (f := fun t : ℝ≥0 => ((t : ℝ)/NativeHeatObservation.timeScale,u))
    (g := fun p : ℝ × Physical (d := d) => VectorHeat.heat p.1 p.2) VectorHeat.continuous_action hi

end SHEStochastic.MatrixContinuousMild
