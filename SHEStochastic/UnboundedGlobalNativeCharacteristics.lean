module

public import SHEStochastic.UnboundedGlobalJointNativePasting
public import SHEStochastic.JointCharacteristicBrownian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.UnboundedGlobalNativeCharacteristics
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting UnboundedNativeHeatEquation UnboundedGlobalUniformRegularity
open UnboundedGlobalJointCanonicalPathMartingale
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)

include hH hnull hEquation hM hu₀ in
/-- The actual native pasting retains every finite driver characteristic
martingale tested against the entire state-driver past. The Borel
continuation kernel is the one already constructed at the exit law. -/
theorem law_identity (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H))
    (hLaw : CanonicalInitialKernel.initialLaw H Q.toMeasure =
      UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput H Q.toMeasure)
    {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) :
    PastedCharacteristicMartingale.Identity H
      (JointDriverCharacteristic.row (V := RealL2) a r) (GaussianCharacteristicMartingale.variance a r)
      (StoppedContinuationMeasure.law H (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint H Q.toMeasure)) := by
  let K := H
  let X := path F μ H W P hcW
  let exit := uniformExit H W hcW R
  let Z := StoppedContinuationMeasure.state K X exit
  have hZ : Measurable Z := StoppedContinuationMeasure.measurable_state K X exit
    (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
  have hp : MeasurePreserving (fun ω ↦ (Z ω).1) μ (CanonicalInitialKernel.initialLaw K Q.toMeasure) := by
    refine ⟨measurable_fst.comp hZ, ?_⟩
    rw [hLaw]
    rfl
  apply PastedCharacteristicMartingale.law_identity K (JointDriverCharacteristic.row a r)
    (GaussianCharacteristicMartingale.variance a r) μ X exit
    (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
    (NativeContinuationKernel.joint K Q.toMeasure) (GaussianCharacteristicMartingale.variance_nonneg a r)
  · filter_upwards [hp.quasiMeasurePreserving.ae
      (NativeContinuationCharacteristics.properties K Q.toMeasure hBrown)] with ω hω
    exact hω (Z ω).2 n a r
  · intro s t hst test htest
    apply JointDriverCharacteristic.stopped_identity F μ K
      (NativeRandomInitialKernel.restrict F μ H P K le_rfl) X
      (adapted_path F μ H W hW P hcW) ?_ exit ?_ a r s t hst test htest
    · intro ω t i
      change (P.W i t.val.toNNReal ω-P.W i 0 ω)-
        (P.W i (0 : ℝ).toNNReal ω-P.W i 0 ω) =
          P.W i (AdaptedCanonicalPathTests.toNN K t) ω-P.W i 0 ω
      rw [Real.toNNReal_zero]
      have ht : t.val.toNNReal = AdaptedCanonicalPathTests.toNN K t :=
        NNReal.eq (Real.coe_toNNReal t.val t.property.1)
      rw [ht]
      ring
    · exact UnboundedGlobalUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀
        hH hcW hnull hEquation M hM hu₀ R

include hH hnull hEquation hM hu₀ in
/-- The actual pasted law has a complete native Brownian driver in its
full state-driver filtration, including all different-time finite laws. -/
def family (R : ℕ)
    (Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H))
    (hLaw : CanonicalInitialKernel.initialLaw H Q.toMeasure =
      UnboundedGlobalExitInitialLaw.law H W hcW R μ)
    (hBrown : NativeContinuationCharacteristics.BrownianInput H Q.toMeasure) :
    FiniteScalarIto.Family (JointPathFiltration.filtration (E := RealL2) (ι := ι) H)
      (StoppedContinuationMeasure.law H (path F μ H W P hcW) (uniformExit H W hcW R)
        (measurable_path F μ H W hW P hcW) (UnboundedGlobalContinuation.exit_measurable F H W hW hcW R)
        μ (NativeContinuationKernel.joint H Q.toMeasure)) H ι := by
  apply JointCharacteristicBrownian.family H _ F μ
    (NativeRandomInitialKernel.restrict F μ H P H le_rfl)
  intro n a r
  exact law_identity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀
    R Q hLaw hBrown a r

end SHEStochastic.UnboundedGlobalNativeCharacteristics
