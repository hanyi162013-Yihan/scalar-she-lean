module
public import SHE.NativeFrozenGaussianCurve
public import SHE.GaussianSeparatedCoordinates
public import SHE.GaussianRowGramCurve

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeFrozenGaussianBlocks
open Set MeasureTheory Filter GaussianMatrixGramCurve GaussianRowGramCurve
open NativeFrozenGaussianRows GaussianContinuity ControlledProfile GaussianCovariancePath
open OrthogonalItoChannels FiniteHaar StoppedFourier
open scoped NNReal ENNReal Matrix.Norms.Elementwise
local instance unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeSigma:MeasurableSpace CircleL2:=borel _
local instance nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance bothSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance bothBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
variable (v b:ℝ≥0) (hvb:v≤b) (P:CanonicalCovariance.ProfileParameters) (Λ κ:ℝ) (hκ:0<κ) (hκP:κ<P.lower)
variable{n:ℕ}(side:Fin n→Bool) (ξ:Fin n→ℝ) (center:Fin n→HeatCircle)
local notation "r" p=>NativeFrozenGaussianRows.raw v b P Λ κ hκ hκP side ξ center p


local notation "C" p=>NativeFrozenGaussianCurve.curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p

theorem covariance_entry (p:Inputs) (i j:Fin n):
    ((C p).path (v:ℝ)).val i j=
      ∫t in (v:ℝ)..(b:ℝ),inner ℝ ((r p) i t) ((r p) j t):=by
  have hh:=GaussianMatrixGramCurve.path_eq
    (NativeFrozenGaussianCurve.density 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p)
    (show (v:ℝ)∈Icc (v:ℝ) (b:ℝ) from ⟨le_rfl,by exact_mod_cast hvb⟩)
  exact congrArg (fun A:MeasurableGeneralizedInverse.Mat n=>A i j) hh

theorem cross_zero (p:Inputs) (i j:Fin n) (hi:side i=false) (hj:side j=true):
    ((C p).path (v:ℝ)).val i j=0:=by
  rw [covariance_entry]
  have he(t:ℝ):inner ℝ ((r p) i t) ((r p) j t)=0:=by
    simp only [NativeFrozenGaussianRows.raw,hi,hj,Bool.false_eq_true,ite_false,ite_true,
      NativeFrozenGaussianRows.lift]
    exact OrthogonalItoChannels.inner_left_right _ _
  simp only [he,intervalIntegral.integral_zero]

/-- The actual common additive and compatible residual coordinate
blocks are independent under the actual conditional Gaussian law. The
residual block keeps its full original shared-noise covariance. -/
theorem independent (p:Inputs){a d:ℕ}(f:Fin a→Fin n)(g:Fin d→Fin n)
    (hf:∀i,side (f i)=false)(hg:∀j,side (g j)=true):
    ProbabilityTheory.IndepFun (GaussianCoordinates.projection f) (GaussianCoordinates.projection g)
      (ProbabilityTheory.multivariateGaussian 0 ((C p).path (v:ℝ)).val):=
  GaussianSeparatedCoordinates.independent f g ((C p).path (v:ℝ)).property
    (fun i j=>cross_zero 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p _ _ (hf i) (hg j))

end SHE.NativeFrozenGaussianBlocks
