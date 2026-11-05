module
public import SHE.SingleNativeHeatEquation
public import SHE.StandardIndependentProductIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace SHE.SingleNativeIndependentExtension
open MeasureTheory Set PredictableL2 NativeHeatObservation
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance extension_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance extension_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance extension_realSecond:SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance extension_realSigma:MeasurableSpace RealL2:=borel _
local instance extension_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance extension_bothSigma:MeasurableSpace (Both RealL2):=borel _
local instance extension_bothBorel:BorelSpace (Both RealL2):=⟨rfl⟩
variable {Ω Ξ:Type*}[MeasurableSpace Ω][MeasurableSpace Ξ]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
variable (μ:Measure Ω)(ν:Measure Ξ)[IsProbabilityMeasure μ][IsProbabilityMeasure ν](H:ℝ≥0)
variable (D:SmoothApproximation.ScalarData)
variable (J:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)(u₀:RealL2)
variable (S:SingleNativeHeatEquation.Data 𝓕 μ H D J u₀)

def value(q:ℝ≥0)(z:IndependentNoiseCompletion.Space μ ν):RealL2:=S.value q z.1

theorem predictable:StronglyMeasurable[(IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖).predictable]
    (Function.uncurry (value 𝓕 μ ν H D J u₀ S)):=
  IndependentNoiseCompletion.state_predictable μ ν 𝓕 𝓖 S.value S.predictable

theorem energy_fst:MeasurePreserving
    (fun p:ℝ≥0×IndependentNoiseCompletion.Space μ ν=>(p.1,p.2.1))
    (energyMeasure (IndependentNoiseCompletion.measure μ ν) H) (energyMeasure μ H):=
  (MeasurePreserving.id (PredictableL2.timeMeasure H)).prod (IndependentNoiseCompletion.fst_preserving μ ν)

/-- The actual enlarged observation row is exactly the original physical
row pulled back to the first coordinate, with zero auxiliary coordinate.
Every predictable-L2 realization and exceptional set is derived here. -/
theorem row_pullback{T t:ℝ}(ht:t<T)(x:HeatCircle):
    PredictableScalarHaarRotation.originalRow
      (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H D
      (Function.uncurry (value 𝓕 μ ν H D J u₀ S)) (predictable 𝓕 𝓖 μ ν H D J u₀ S) ht x
      =ᵐ[energyMeasure (IndependentNoiseCompletion.measure μ ν) H]
      (fun p=>WithLp.toLp 2
        (SingleNativeHeatEquation.row 𝓕 μ H D (Function.uncurry S.value) S.predictable ht x (p.1,p.2.1),0)):=by
  have hs:=(energy_fst μ ν H).quasiMeasurePreserving.ae
    (SingleNativeHeatEquation.row_ae 𝓕 μ H D (Function.uncurry S.value) S.predictable ht x)
  have ho:=PredictableScalarHaarRotation.originalRow_ae
    (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H D
    (Function.uncurry (value 𝓕 μ ν H D J u₀ S)) (predictable 𝓕 𝓖 μ ν H D J u₀ S) ht x
  filter_upwards [ho,hs] with p ho hs
  rw [ho,hs]
  by_cases hp:(p.1:ℝ)<t
  · rw [if_pos hp,if_pos hp]
    rfl
  · rw [if_neg hp,if_neg hp]
    rfl

variable (Kaux:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓖 ν H)
variable (P:IndependentProductItoData (C:=RealL2) 𝓕 𝓖 μ ν H J Kaux)

include P in
/-- Ordinary product-Ito naturality transports the GIVEN one-noise
observable equation to the augmented space. No enlarged SPDE equation,
mild solution, or solution-law equality is an input. -/
theorem equation:OriginalNativeHeatEquation.Equation
    (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H D P.integral u₀
    (value 𝓕 μ ν H D J u₀ S) (predictable 𝓕 𝓖 μ ν H D J u₀ S):=by
  intro q hq ε hε x
  have ht:(q:ℝ)<(q:ℝ)+ε:=by linarith only [hε]
  let f:=SingleNativeHeatEquation.row 𝓕 μ H D (Function.uncurry S.value) S.predictable ht x
  let g:=PredictableScalarHaarRotation.originalRow
    (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H D
    (Function.uncurry (value 𝓕 μ ν H D J u₀ S)) (predictable 𝓕 𝓖 μ ν H D J u₀ S) ht x
  have hn:=P.first f g (row_pullback 𝓕 𝓖 μ ν H D J u₀ S ht x)
  have hs:=(IndependentNoiseCompletion.fst_preserving μ ν).quasiMeasurePreserving.ae
    (S.equation q hq ε hε x)
  filter_upwards [hs,hn] with z hs hn
  change functional ε x (S.value q z.1)=functional ((q:ℝ)+ε) x u₀+P.integral.integral g z
  rw [hn]
  exact hs

include P in
def of_integral:OriginalNativeHeatEquation.Data
    (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H D P.integral u₀ where
  value:=value 𝓕 μ ν H D J u₀ S
  continuous:=fun z=>S.continuous z.1
  predictable:=predictable 𝓕 𝓖 μ ν H D J u₀ S
  equation:=equation 𝓕 𝓖 μ ν H D J u₀ S Kaux P

/-- Enlarge a supplied one-noise equation by an independent auxiliary
noise, using ONLY the explicitly named ordinary constructor component
of package 1. The state and its actual continuous-path law are preserved
by proved measure-preserving transport. An independent COPY of the
original noise can be used by taking the second space and K equal to
the first; no separate Wiener-measure existence input is needed. -/
theorem exists_extension
    (K:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓖 ν H)
    (hProduct:StandardIndependentProductIto (Ω:=Ω) (Ξ:=Ξ) (C:=RealL2) 𝓕 𝓖 μ ν H J K):
    ∃(B:StandardTerminalIto (C:=Both RealL2) (E:=ℝ)
        (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H)
      (R:OriginalNativeHeatEquation.Data (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖)
        (IndependentNoiseCompletion.measure μ ν) H D B u₀),
      R.value=(fun q (z:IndependentNoiseCompletion.Space μ ν)=>S.value q z.1) ∧
      NativePathLawComparison.law H (IndependentNoiseCompletion.measure μ ν) R.value R.continuous=
        NativePathLawComparison.law H μ S.value S.continuous:=by
  obtain ⟨P⟩:=hProduct.exists_data
  let R:=of_integral 𝓕 𝓖 μ ν H D J u₀ S K P
  refine ⟨P.integral,R,rfl,?_⟩
  exact IndependentNoiseCompletion.state_law μ ν H S.value S.continuous
    ((S.predictable.mono (predictable_le_product 𝓕)).measurable)

end SHE.SingleNativeIndependentExtension
