module
public import SHE.NativeJointRowClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeJointGradientFields
open Set MeasureTheory PredictableL2 Real AddCircle StoppedFourier NativeHeatObservation NativeMovingCurrentGamma ScalarGaussianSemigroup DyadicApproximation
open scoped NNReal ENNReal
local instance jointGradientFields_period : Fact (0<2*π):=⟨by positivity⟩
local instance jointGradientFields_realSigma : MeasurableSpace RealL2:=borel _
local instance jointGradientFields_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance jointGradientFields_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGradientFields_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance jointGradientFields_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance jointGradientFields_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGradientFields_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]

def value (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ) (H:ℝ≥0) (a:ℝ→ℝ) (j:ℕ) (h:ℝ) (p:ℝ×(ℝ×(Ω×HeatCircle))):ℝ:=
  NativeJointRowClock.directGradient P U V Λ H a j p.2.1 h p.1 p.2.2

theorem measurable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (Λ:ℝ) (H:ℝ≥0) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) (j:ℕ) (h:ℝ):
    Measurable (value P U V Λ H a j h):=by
  let Ur:=fun p:ℝ×Ω=>U (p.1.toNNReal,p.2)
  let Dr:=NativePathZeroExtension.extend H (fun p=>V p-U p)
  have hmU:Measurable U:=(hU.mono (predictable_le_product 𝓕)).measurable
  have hmV:Measurable V:=(hV.mono (predictable_le_product 𝓕)).measurable
  have hUr:Measurable Ur:=hmU.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hDr:Measurable Dr:=NativePathZeroExtension.measurable H _ (hmV.sub hmU)
  have hs:=NativeMovingCurrentGamma.variance_measurable P Ur Dr hUr hDr Λ h 0
  have hx:=NativeMovingCurrentGamma.current_measurable Ur hUr h
  have hy:=hx.add (NativeMovingJointGamma.direction_measurable Dr hDr Λ h)
  have hg:Measurable (fun p:ℝ×space Ω=>
      deriv (heat (variance P Ur Dr Λ h 0 p).toNNReal (ScalarHeatBands.band a (j+1)))
        (current Ur h p+NativeMovingJointGamma.direction Dr Λ h p)-
      deriv (heat (variance P Ur Dr Λ h 0 p).toNNReal (ScalarHeatBands.band a (j+1))) (current Ur h p)):=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) _ _ hs hy).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) _ _ hs hx)
  exact hg.comp (measurable_fst.prodMk ((measurable_snd.fst.prodMk measurable_snd.snd.fst).prodMk measurable_snd.snd.snd))

theorem bound (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ) (H:ℝ≥0) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A:ℝ} (hA:0≤A)
    (hh:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ) (h:ℝ) (p:ℝ×(ℝ×(Ω×HeatCircle))):
    |value P U V Λ H a j h p|≤2*ScalarHeatSingleMultiplier.cap A P.exponent j:=by
  let C:=ScalarHeatSingleMultiplier.cap A P.exponent j
  have hb(σ x:ℝ):|deriv (heat σ.toNNReal (ScalarHeatBands.band a (j+1))) x|≤C:=by
    simpa only [C,ScalarHeatSingleMultiplier.cap,iteratedDeriv_one,Nat.zero_add,Nat.cast_zero,sub_zero] using
      ScalarHeatBandJets.heated_positive_jet ha hA P.exponent_pos.le P.exponent_le_one hh σ.toNNReal (j+1) 0 x
  exact (abs_sub _ _).trans ((add_le_add (hb _ _) (hb _ _)).trans_eq (by ring))
end SHE.NativeJointGradientFields
