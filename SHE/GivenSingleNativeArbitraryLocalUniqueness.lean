module
public import SHE.NativeSingleLocalClock
public import SHE.GivenSingleNativeLocalInputs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.GivenSingleNativeArbitraryLocalUniqueness
open MeasureTheory PredictableL2 NativeObservationNaturality DyadicApproximation
open scoped NNReal ENNReal
local instance arbitraryLocal_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance arbitraryLocal_realSecond:SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance arbitraryLocal_realSigma:MeasurableSpace RealL2:=borel _
local instance arbitraryLocal_realBorel:BorelSpace RealL2:=⟨rfl⟩
variable {ι:Type} [Fintype ι] (Ω:ι→Type) [∀i,MeasurableSpace (Ω i)]
variable (F:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
variable (μ:∀i,Measure (Ω i)) [∀i,IsProbabilityMeasure (μ i)]
variable (H:ℝ≥0) (D:SmoothApproximation.ScalarData)
variable (J:∀i,StandardTerminalIto (C:=RealL2) (E:=ℝ) (F i) (μ i) H) (u₀:RealL2)
variable (U:∀i,SingleNativeHeatEquation.Data (F i) (μ i) H D (J i) u₀)

/-- The ordinary input record is evaluated at the exact inverse-clock
recast of the given maps and solutions. No new solution is selected. -/
abbrev Inputs:=GivenSingleNativeLocalInputs.Inputs Ω
  (fun i=>NativeInverseClock.base (F i)) μ (NativeClock.time H) D
  (fun i=>NativeInverseClock.native (F i) (μ i) H (J i)) u₀
  (fun i=>NativeSingleLocalClock.model (μ i) (F i) H D (J i) u₀ (U i))

/-- Local uniqueness on an arbitrary native filtration and prescribed
native horizon. The state paths and the original scalar integrals are
preserved by the exact clock round trip. -/
theorem laws_eq (hH:0<H) (hH1:(H:ℝ)≤1)
    (A:Inputs Ω F μ H D J u₀ U):
    ∀i j:ι,NativePathLawComparison.law H (μ i) (U i).value (U i).continuous=
      NativePathLawComparison.law H (μ j) (U j).value (U j).continuous:=by
  obtain ⟨hp,ht,hn⟩:=NativeSingleLocalClock.bounds H hH hH1
  have h:=GivenSingleNativeLocalInputs.laws_eq Ω
    (fun i=>NativeInverseClock.base (F i)) μ (NativeClock.time H) D
    (fun i=>NativeInverseClock.native (F i) (μ i) H (J i)) u₀
    (fun i=>NativeSingleLocalClock.model (μ i) (F i) H D (J i) u₀ (U i)) ht hp hn A
  intro i j
  exact eq_of_heq ((NativeSingleLocalClock.model_law (μ i) (F i) H D (J i) u₀ (U i)).symm.trans
    ((heq_of_eq (h i j)).trans
      (NativeSingleLocalClock.model_law (μ j) (F j) H D (J j) u₀ (U j))))
end SHE.GivenSingleNativeArbitraryLocalUniqueness
