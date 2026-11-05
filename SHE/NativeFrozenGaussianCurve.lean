module
public import SHE.NativeFrozenGaussianRows
public import SHE.GaussianRowGramCurve

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeFrozenGaussianCurve
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
local instance bothSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance bothBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
variable (v b:ℝ≥0) (hvb:v≤b) (P:CanonicalCovariance.ProfileParameters) (Λ κ:ℝ) (hκ:0<κ) (hκP:κ<P.lower)
variable{n:ℕ}(side:Fin n→Bool) (ξ:Fin n→ℝ) (center:Fin n→HeatCircle)
local notation "r" p=>NativeFrozenGaussianRows.raw v b P Λ κ hκ hκP side ξ center p

def density (p:Inputs):GaussianMatrixGramCurve.Density n:=
  GaussianRowGramCurve.density (r p)
    (NativeFrozenGaussianRows.raw_measurable 𝓕 μ v b P Λ κ hκ hκP side ξ center p)
    (v:ℝ) (b:ℝ) (by exact_mod_cast hvb)
    (NativeFrozenGaussianRows.raw_square_integrable 𝓕 μ v b P Λ κ hκ hκP side ξ center hvb p)

def curve (p:Inputs):GaussianMatrixCurve.Curve n:=GaussianMatrixGramCurve.curve (density 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p)

variable (hΛ:0≤Λ) (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hΛ hsmall in
theorem gram_parameter_continuous (t:ℝ):Continuous (fun p:Inputs=>GaussianRowGramCurve.gram (r p) t):=by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (NativeFrozenGaussianRows.raw_parameter_continuous v b P Λ κ hκ hκP side ξ center hΛ hsmall i t).inner
    (𝕜:=ℝ) (NativeFrozenGaussianRows.raw_parameter_continuous v b P Λ κ hκ hκP side ξ center hΛ hsmall j t)

include 𝓕 μ hΛ hsmall in
theorem gram_joint_measurable:Measurable (fun z:Inputs×ℝ=>GaussianRowGramCurve.gram (r z.1) z.2):=by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact continuous_inner.measurable.comp
    ((NativeFrozenGaussianRows.raw_joint_measurable 𝓕 μ v b P Λ κ hκ hκP side ξ center hΛ hsmall i).prodMk
      (NativeFrozenGaussianRows.raw_joint_measurable 𝓕 μ v b P Λ κ hκ hκP side ξ center hΛ hsmall j))

theorem gram_bound (p:Inputs){t:ℝ}(ht0:0≤t) (htb:t<(b:ℝ)) (i j:Fin n):
    ‖GaussianRowGramCurve.gram (r p) t i j‖≤P.upper*(1+heatConstant*((b:ℝ)-t)^(-(1/2:ℝ))):=by
  have hi:=NativeFrozenGaussianRows.raw_bound v b P Λ κ hκ hκP side ξ center p i ht0 htb
  have hj:=NativeFrozenGaussianRows.raw_bound v b P Λ κ hκ hκP side ξ center p j ht0 htb
  have hn:=norm_inner_le_norm (𝕜:=ℝ) ((r p) i t) ((r p) j t)
  have hs:=sq_nonneg (‖(r p) i t‖-‖(r p) j t‖)
  change ‖inner ℝ ((r p) i t) ((r p) j t)‖≤_
  nlinarith

include hΛ hsmall in
theorem covariance_parameter_continuous (t:ℝ):
    Continuous (fun p:Inputs=>(curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p).path t):=by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  let a:=ClippedCovariance.clip (v:ℝ) (b:ℝ) t
  have ha:=ClippedCovariance.clip_mem (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb) t
  have he : (fun p:Inputs=>((curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p).path t).val i j)=
      fun p:Inputs=>∫s:ℝ,GaussianRowGramCurve.gram (r p) s i j ∂volume.restrict (Ioc a (b:ℝ)) := by
    funext p
    exact intervalIntegral.integral_of_le ha.2
  change Continuous (fun p:Inputs=>((curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p).path t).val i j)
  rw [he]
  apply continuous_of_dominated (bound:=fun s:ℝ=>P.upper*(1+heatConstant*((b:ℝ)-s)^(-(1/2:ℝ))))
  · intro p
    exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (GaussianRowGramCurve.gram_measurable (r p)
        (NativeFrozenGaussianRows.raw_measurable 𝓕 μ v b P Λ κ hκ hκP side ξ center p))))).aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with s hs hne
    exact gram_bound v b P Λ κ hκ hκP side ξ center p (v.2.trans (ha.1.trans hs.1.le)) (lt_of_le_of_ne hs.2 hne) i j
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q:=a) (s:=(b:ℝ)) P.upper).1
  · filter_upwards with s
    exact ((continuous_apply j).comp (continuous_apply i)).comp
      (gram_parameter_continuous v b P Λ κ hκ hκP side ξ center hΛ hsmall s)

include hΛ hsmall in
theorem path_joint_measurable:Measurable (fun z:Inputs×ℝ=>(curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center z.1).path z.2):=by
  exact measurable_uncurry_of_continuous_of_measurable
    (covariance_parameter_continuous 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center hΛ hsmall)
    (fun p=>(curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center p).continuous_path.measurable)

end SHE.NativeFrozenGaussianCurve
