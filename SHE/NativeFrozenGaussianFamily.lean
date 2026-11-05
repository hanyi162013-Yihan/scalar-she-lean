module
public import SHE.NativeFrozenGaussianCurve
public import SHE.GaussianMatrixFamily

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeFrozenGaussianFamily
open Set MeasureTheory PredictableL2 GaussianMatrixFamily NativeFrozenGaussianRows
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

def family (m:Inputs→WordRecursion.State n) (hm:Continuous m):Family Inputs n where
  left:=v
  right:=b
  curve:=Curve
  left_eq:=fun _=>rfl
  right_eq:=fun _=>rfl
  path_measurable:=NativeFrozenGaussianCurve.path_joint_measurable 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center hΛ hsmall
  path_parameter_continuous:=NativeFrozenGaussianCurve.covariance_parameter_continuous 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center hΛ hsmall
  density_measurable:=NativeFrozenGaussianCurve.gram_joint_measurable 𝓕 μ v b P Λ κ hκ hκP side ξ center hΛ hsmall
  density_parameter_continuous:=Filter.Eventually.of_forall
    (NativeFrozenGaussianCurve.gram_parameter_continuous v b P Λ κ hκ hκP side ξ center hΛ hsmall)
  center:=m
  center_continuous:=hm

variable (H:ℝ≥0) (hbH:b≤H) (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data)
local notation "R"=>NativeFrozenGaussianRows.rows 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH
local notation "Q"=>GaussianStoppedRows.rows 𝓕 μ H v b R

/-- The actual random-past native rows have the genuine diagonal
matrix Gram on one original energy event. Fubini is applied only after
that whole-field identity, so no fixed-parameter exceptional set is used. -/
theorem bracket:
    ∀ᵐω∂μ,∀ᵐt:ℝ,t∈Ioo (v:ℝ) (b:ℝ)→
      StandardFiniteIto.rowCovariance 𝓕 μ H Q ω t=(Curve (data ω)).density t:=by
  have he:∀ᵐz∂energyMeasure μ H,∀i,v<z.1 ∧ z.1<b→Q i z=
      NativeFrozenGaussianRows.raw v b P Λ κ hκ hκP side ξ center (data z.2) i (z.1:ℝ):=by
    filter_upwards [ae_all_iff.mpr (fun i=>GaussianStoppedRows.rows_ae 𝓕 μ H v b R i),
      ae_all_iff.mpr (NativeFrozenGaussianRows.rows_ae 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH)] with z hq hr
    intro i hi
    rw [hq i,ite_eq_left hi]
    exact hr i hi
  have hs:=(Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  have hre:∀ᵐt:ℝ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t∈Ioo (v:ℝ) (b:ℝ)→
      StandardFiniteIto.rowCovariance 𝓕 μ H Q ω t=(Curve (data ω)).density t:=by
    rw [←timeMeasure_map H]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hω] with t ht htin
    simp only [Prod.swap] at ht
    have hti:v<t ∧ t<b:=by exact_mod_cast htin
    ext i j
    change inner ℝ (Q i ((t:ℝ).toNNReal,ω)) (Q j ((t:ℝ).toNNReal,ω))=
      inner ℝ (NativeFrozenGaussianRows.raw v b P Λ κ hκ hκP side ξ center (data ω) i (t:ℝ))
        (NativeFrozenGaussianRows.raw v b P Λ κ hκ hκP side ξ center (data ω) j (t:ℝ))
    simp only [Real.toNNReal_coe]
    rw [ht i hti,ht j hti]
  rw [ae_restrict_iff' measurableSet_Ioc] at hre
  filter_upwards [hre] with t ht htin
  exact ht ⟨v.2.trans_lt htin.1,htin.2.le.trans (by exact_mod_cast hbH)⟩ htin

end SHE.NativeFrozenGaussianFamily
