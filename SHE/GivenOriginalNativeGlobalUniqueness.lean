module
public import SHE.OriginalConditionalFamilyStep
public import SHE.NativeFamilyPathMeshExtension
public import SHE.NativeZeroPathLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.GivenOriginalNativeGlobalUniqueness
open MeasureTheory ProbabilityTheory Set PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open scoped NNReal ENNReal
local instance globalOriginal_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance globalOriginal_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance globalOriginal_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance globalOriginal_realSigma:MeasurableSpace RealL2:=borel _
local instance globalOriginal_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance globalOriginal_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance globalOriginal_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance globalOriginal_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance globalOriginal_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable{ι:Type}[Fintype ι][Nonempty ι](Ω:ι→Type)[∀i,MeasurableSpace (Ω i)]
variable(F:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
variable(μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)]
variable(H:ℝ≥0)(D:SmoothApproximation.ScalarData)
variable(B:∀i,StandardTerminalIto (C:=Both RealL2) (E:=ℝ) (F i) (μ i) H)(u₀:RealL2)
variable(S:∀i,OriginalNativeHeatEquation.Data (F i) (μ i) H D (B i) u₀)

/-- Arbitrary finite-horizon uniqueness of the actual original heat
observed equations. Conditional weak models, same-initial local law
comparison, state-kernel projection and the finite prefix induction are
all instantiated internally. The explicit inputs are only the ordinary
stochastic packages on the actual original and selected conditional maps.
No conditional SPDE equation, future-law equality, Markov property or
uniqueness conclusion is supplied as a hypothesis. -/
theorem laws_eq(hpos:0<H)(C:ι→ℝ≥0)
    (hBDG:∀i,StandardTerminalBDG16 (B i) (C i))
    (hnull:∀i,NullCompleteFiltration.ContainsNullSets (F i) (μ i))
    (hLevy:∀i,StandardTerminalLevy (B i))
    (hlocal:∀i,StandardTerminalPastLocality (B i))
    (hConstruct:∀v h:ℝ≥0,0<h→h≤1→v+h≤H→∀i p,
      StandardBrownianItoConstruction (ConditionalCanonicalModelFamily.filtration h)
        (OriginalConditionalFamilyStep.kernel Ω F μ H D B u₀ S v h hpos i p)
        h NativeSingleNoiseBasis.basis (CanonicalStateDriverFiltration.coordinate h))
    (hInputs:∀v h:ℝ≥0,0<h→h≤1→v+h≤H→
      (∀i j,OriginalConditionalFamilyStep.pastLaw Ω F μ H D B u₀ S v i=
        OriginalConditionalFamilyStep.pastLaw Ω F μ H D B u₀ S v j)→
      OriginalConditionalFamilyStep.OrdinaryInputs Ω F μ H D B u₀ S v h hpos):
    ∀i j:ι,(μ i).map (NativeContinuousPath.path H (S i).value (S i).continuous)=
      (μ j).map (NativeContinuousPath.path H (S j).value (S j).continuous):=by
  apply NativeFamilyPathMeshExtension.arbitrary_horizon Ω μ
    (fun i=>(S i).value) (fun i=>(S i).continuous)
    (fun i=>((S i).predictable.mono (predictable_le_product (F i))).measurable)
    H 1 zero_lt_one
  · intro i j
    exact (NativeZeroPathLaw.dirac (μ i) (S i).value (S i).continuous u₀
      (OriginalNativePastIncrement.initial (F i) (μ i) H D (B i) u₀ (S i))).trans
      (NativeZeroPathLaw.dirac (μ j) (S j).value (S j).continuous u₀
        (OriginalNativePastIncrement.initial (F j) (μ j) H D (B j) u₀ (S j))).symm
  · intro v h hh hs hvh hp
    exact OriginalConditionalFamilyStep.future_eq Ω F μ H D B u₀ S v h hpos
      hvh hh (by exact_mod_cast hs) C hBDG hnull hLevy hlocal
      (hConstruct v h hh hs hvh) hp (hInputs v h hh hs hvh hp)
end SHE.GivenOriginalNativeGlobalUniqueness
