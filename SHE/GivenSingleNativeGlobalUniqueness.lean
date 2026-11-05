module
public import SHE.SingleNativeGlobalFamily
public import SHE.GivenOriginalNativeGlobalUniqueness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.GivenSingleNativeGlobalUniqueness
open MeasureTheory ProbabilityTheory Set PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal
local instance bareGlobal_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance bareGlobal_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance bareGlobal_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance bareGlobal_realSigma:MeasurableSpace RealL2:=borel _
local instance bareGlobal_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance bareGlobal_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance bareGlobal_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
variable {ι:Type} [Fintype ι] [Nonempty ι] (Ω:ι→Type) [∀i,MeasurableSpace (Ω i)]
variable (F:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
variable (μ:∀i,Measure (Ω i)) [∀i,IsProbabilityMeasure (μ i)] (H:ℝ≥0)
variable (D:SmoothApproximation.ScalarData)
variable (J:∀i,StandardTerminalIto (C:=RealL2) (E:=ℝ) (F i) (μ i) H) (u₀:RealL2)
variable (S:∀i,SingleNativeHeatEquation.Data (F i) (μ i) H D (J i) u₀)
variable (P:SingleNativeGlobalFamily.Products Ω F μ H J) (hpos:0<H)

/-- The accepted ordinary stochastic packages, on the actual independent
copy enlargement and selected conditional product/rotated maps. This
record contains no estimate, SPDE restart, conditional future-law equality,
comparison, weak existence, or uniqueness conclusion. Package1's ordinary
independent-product constructor is the separate explicit parameter P.
The remaining conditional local packages are required only almost surely
under the actual state-prefix laws, after their equality is established. -/
structure Inputs where
  C:ι→ℝ≥0
  bdg:∀i,StandardTerminalBDG16 (SingleNativeGlobalFamily.physical Ω F μ H J P i) (C i)
  levy:∀i,StandardTerminalLevy (SingleNativeGlobalFamily.physical Ω F μ H J P i)
  locality:∀i,StandardTerminalPastLocality (SingleNativeGlobalFamily.physical Ω F μ H J P i)
  construction:∀v h:ℝ≥0,0<h→h≤1→v+h≤H→∀i p,
    StandardBrownianItoConstruction (ConditionalCanonicalModelFamily.filtration h)
      (OriginalConditionalFamilyStep.kernel (SingleNativeGlobalFamily.Space Ω μ)
        (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
        (SingleNativeGlobalFamily.physical Ω F μ H J P) u₀
        (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P) v h hpos i p)
      h NativeSingleNoiseBasis.basis (CanonicalStateDriverFiltration.coordinate h)
  localPackages:∀v h:ℝ≥0,0<h→h≤1→v+h≤H→
    (∀i j,OriginalConditionalFamilyStep.pastLaw (SingleNativeGlobalFamily.Space Ω μ)
        (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
        (SingleNativeGlobalFamily.physical Ω F μ H J P) u₀
        (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P) v i=
      OriginalConditionalFamilyStep.pastLaw (SingleNativeGlobalFamily.Space Ω μ)
        (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
        (SingleNativeGlobalFamily.physical Ω F μ H J P) u₀
        (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P) v j)→
    OriginalConditionalFamilyStep.OrdinaryInputs (SingleNativeGlobalFamily.Space Ω μ)
      (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
      (SingleNativeGlobalFamily.physical Ω F μ H J P) u₀
      (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P) v h hpos

/-- Bounded scalar weak uniqueness for GIVEN bare single-noise original
positive-heat equations, on arbitrary probability spaces and arbitrary
positive finite native horizon. The original continuous state-path laws
are equal. Independent-noise enlargement, all comparison estimates,
conditional weak models, local applications, finite global continuation,
and exact transport back to the original spaces are proved internally.
Only the explicitly accepted seven ordinary stochastic packages remain. -/
theorem laws_eq (A:Inputs Ω F μ H D J u₀ S P hpos) :
    ∀i j:ι,NativePathLawComparison.law H (μ i) (S i).value (S i).continuous=
      NativePathLawComparison.law H (μ j) (S j).value (S j).continuous := by
  have hg := GivenOriginalNativeGlobalUniqueness.laws_eq (SingleNativeGlobalFamily.Space Ω μ)
    (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
    (SingleNativeGlobalFamily.physical Ω F μ H J P) u₀
    (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P) hpos A.C A.bdg
    (SingleNativeGlobalFamily.contains_null Ω F μ) A.levy A.locality A.construction A.localPackages
  have he (i j:ι) : NativePathLawComparison.law H (SingleNativeGlobalFamily.measure Ω μ i)
      (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P i).value
      (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P i).continuous=
    NativePathLawComparison.law H (SingleNativeGlobalFamily.measure Ω μ j)
      (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P j).value
      (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S P j).continuous := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hg i j
  intro i j
  exact (SingleNativeGlobalFamily.same_law Ω F μ H J D u₀ S P i).symm.trans
    ((he i j).trans (SingleNativeGlobalFamily.same_law Ω F μ H J D u₀ S P j))
end SHE.GivenSingleNativeGlobalUniqueness
