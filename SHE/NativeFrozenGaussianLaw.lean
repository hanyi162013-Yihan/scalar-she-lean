module
public import SHE.NativeFrozenGaussianTransition
public import SHE.RandomGaussianMatrixIto
public import SHE.GaussianStandardRealization

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeFrozenGaussianLaw
open Set MeasureTheory ProbabilityTheory PredictableL2 GaussianMatrixFamily NativeFrozenGaussianRows
open GaussianMatrixGramCurve ControlledProfile OrthogonalItoChannels FiniteHaar StoppedFourier
open scoped NNReal ENNReal
local instance period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
variable (v b:ℝ≥0) (hvb:v≤b) (P:CanonicalCovariance.ProfileParameters) (Λ κ:ℝ) (hκ:0<κ) (hκP:κ<P.lower)
variable {n:ℕ}(side:Fin n→Bool) (ξ:Fin n→ℝ) (center:Fin n→HeatCircle)
variable (hΛ:0≤Λ) (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
local notation "Curve"=>NativeFrozenGaussianCurve.curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center

variable (H:ℝ≥0) (hbH:b≤H) (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data)
local notation "R"=>NativeFrozenGaussianRows.rows 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH
local notation "Q"=>GaussianStoppedRows.rows 𝓕 μ H v b R


variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
local notation "Y"=>SingularVectorIntegral.value 𝓕 μ H b J (0:WordRecursion.State n) Q


local notation "Cov" p=>(Curve p).path (v:ℝ)

def terminal (m:Inputs→WordRecursion.State n) (ω:Ω):WordRecursion.State n:=
  GaussianStoppedRows.terminal 𝓕 μ H v b R J 0 ω+m (data ω)

theorem terminal_measurable (m:Inputs→WordRecursion.State n) (hm:Continuous m):
    Measurable (terminal 𝓕 μ v b P Λ κ hκ hκP side ξ center H hbH data hdata J m):=by
  apply Measurable.add
  · apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_const.add (Lp.stronglyMeasurable _).measurable
  · exact hm.measurable.comp (hdata.mono (𝓕.le v) le_rfl)

include hΛ hsmall in
/-- The actual compatible frozen observations have this explicit common
standard-Gaussian realization in law. Thus bounded nonsmooth displacement
minima transfer with the SAME past data and covariance mixture. -/
theorem law (hb0:0<b) (hb1:(b:ℝ)≤1)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hlocal:StandardTerminalPastLocality J)
    (m:Inputs→WordRecursion.State n) (hm:Continuous m):
    HasLaw (terminal 𝓕 μ v b P Λ κ hκ hκP side ξ center H hbH data hdata J m)
      ((μ.prod (stdGaussian (WordRecursion.State n))).map
        (GaussianStandardRealization.simulated (fun p=>Cov p) m data)) μ:=by
  apply GaussianStandardRealization.hasLaw (fun p=>Cov p) m μ
    (NativeFrozenGaussianCurve.covariance_parameter_continuous 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center hΛ hsmall v)
    hm data (hdata.mono (𝓕.le v) le_rfl) _ (terminal_measurable 𝓕 μ v b P Λ κ hκ hκP side ξ center H hbH data hdata J m hm)
  intro F hF
  simpa only [Measure.restrict_univ,terminal] using
    NativeFrozenGaussianTransition.conditional_smooth 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center hΛ hsmall
      H hbH data hdata J hb0 hb1 hnull B hBDG hJ hlocal m hm hF univ MeasurableSet.univ

end SHE.NativeFrozenGaussianLaw
