module

public import SHEStochastic.NativeDeterministicShift
public import SHEStochastic.NativeHorizonRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeHorizonIntegral
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H K : ℝ≥0}

theorem filtration_zero : DeterministicItoShift.filtration F 0=F := by
  apply Filtration.ext
  funext t
  change F (0+t)=F t
  rw [zero_add]

def castInput {D : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (h : D=F)
    (u : Process (E := C) F μ K) : Process (E := C) D μ K := h.symm ▸ u

theorem castInput_apply {D : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (h : D=F)
    (u : Process (E := C) F μ K) (p : ℝ≥0×Ω) : castInput (F := F) (μ := μ) (K := K) (C := C) h u p=u p := by
  cases h
  rfl

def castFamily {D : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (h : D=F)
    (Q : FiniteScalarIto.Family F μ K ι) : FiniteScalarIto.Family D μ K ι := h.symm ▸ Q

theorem castFamily_W {D : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (h : D=F)
    (Q : FiniteScalarIto.Family F μ K ι) : (castFamily (F := F) (μ := μ) (K := K) h Q).W=Q.W := by
  cases h
  rfl

theorem cast_integral {D : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (h : D=F)
    (Q : FiniteScalarIto.Family F μ K ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ K) :
    (FiniteCylindricalIto.terminalIto (castFamily (F := F) (μ := μ) (K := K) h Q).toCoordinates e).integral (castInput (F := F) (μ := μ) (K := K) (C := C) h u)=
      (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral u := by
  cases h
  rfl

def shifted (Q : FiniteScalarIto.Family F μ K ι) :
    FiniteScalarIto.Family (DeterministicItoShift.filtration F 0) μ K ι := castFamily (F := F) (μ := μ) (K := K) filtration_zero Q

def shiftedInput (u : Process (E := C) F μ K) :
    Process (E := C) (DeterministicItoShift.filtration F 0) μ K := castInput (F := F) (μ := μ) (K := K) (C := C) filtration_zero u

private theorem shiftedInput_ae (u : Process (E := C) F μ K) :
    shiftedInput u =ᵐ[energyMeasure μ K] u :=
  Filter.Eventually.of_forall (castInput_apply (F := F) (μ := μ) (K := K) (C := C) filtration_zero u)

/-- Extend the actual predictable input by zero to a larger terminal
horizon. The only change is the input's time measure. -/
def input (hKH : K≤H) (u : Process (E := C) F μ K) : Process (E := C) F μ H :=
  DeterministicItoShift.input F μ H 0 K (by simpa using hKH) (shiftedInput u)

theorem input_ae (hKH : K≤H) (u : Process (E := C) F μ K) :
    input hKH u =ᵐ[energyMeasure μ H] DeterministicItoShift.extend 0 K u := by
  have hu := DeterministicItoShift.input_ae F μ H 0 K (by simpa using hKH) (shiftedInput u)
  have hm : @Measurable _ _ (DeterministicItoShift.filtration F 0).predictable _ u := by
    rw [filtration_zero]
    exact (Lp.stronglyMeasurable u).measurable
  exact hu.trans (DeterministicItoShift.extend_ae F μ H 0 K (by simpa using hKH)
    (Lp.stronglyMeasurable (shiftedInput u)).measurable hm (shiftedInput_ae u))

/-- The native stochastic integral is independent of the terminal
horizon whenever the original coordinate paths agree there. -/
theorem integral (hKH : K≤H) (P : FiniteScalarIto.Family F μ H ι)
    (Q : FiniteScalarIto.Family F μ K ι) (e : HilbertBasis ι ℝ C)
    (hW : ∀ i t,t≤K → Q.W i t =ᵐ[μ] P.W i t)
    (u : Process (E := C) F μ K) :
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e).integral u=
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (input hKH u) := by
  have hz (i : ι) : P.W i 0 =ᵐ[μ] fun _ => 0 := by
    have hi := FiniteCylindricalIto.coordinate_integral P e i 0 bot_le
    simp only [NNReal.coe_zero,StoppedItoInputs.stop_zero,map_zero] at hi
    exact hi.symm.trans (Lp.coeFn_zero _ _ _)
  have hw (i : ι) (t : ℝ≥0) (ht : t≤K) :
      (shifted Q).W i t =ᵐ[μ] fun ω => P.W i (0+t) ω-P.W i 0 ω := by
    filter_upwards [hW i t ht,hz i] with ω ht hz
    rw [show (shifted Q).W=Q.W from castFamily_W (F := F) (μ := μ) (K := K) filtration_zero Q,zero_add,hz,sub_zero]
    exact ht
  have hi := NativeDeterministicShift.integral_ae (by simpa using hKH : 0+K≤H) P (shifted Q) e hw (shiftedInput u)
  exact (cast_integral (F := F) (μ := μ) (K := K) (C := C) filtration_zero Q e u).symm.trans hi

end SHEStochastic.NativeHorizonIntegral
