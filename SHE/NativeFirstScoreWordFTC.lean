module
public import SHE.NativeFirstScoreReserve
public import SHE.GaussianFixedFirstAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeFirstScoreWordFTC
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution FiniteCenteredProduct
  ControlledProfile StoppedFourier PhysicalMeanRange StoppedGaussianFeatures StoppedGaussianScore ProfilePointwise ProfileParameter ProfileStability
open scoped BigOperators NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X ι:Type*} [MeasurableSpace X] [DecidableEq ι] {n:ℕ}
variable (P:CanonicalCovariance.ProfileParameters) {Λ:ℝ} (hΛ:0≤Λ)
variable (σ target:Fin n→ℝ) (center:Fin n→UnitAddCircle) (q:ℝ) (hq:0≤q)
variable (hgap:∀i,q<σ i) (hTh:∀i,σ i≤P.horizon) (hages:∀i,σ i≤target i)
variable (u d Z D:CircleL2) (old:ControlledProfile.Domain→ℝ) (hold:Measurable old)
variable (holdb:∀p,0≤old p ∧ old p≤P.lower/2)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (μ:Measure X) [SFinite μ] (w:X→ℝ)(hw:Integrable w μ)(hwm:Measurable w)
variable (shift:X→State n)(hs:Measurable shift) (e:State n)
variable (s:Finset ι)(leaf:ι→ControlledProfile.Domain)
variable (Rtest:State n→ℝ)(a:ι→State n→ℝ)(hRoot:Measurable Rtest)(ha:∀i∈s,Measurable (a i))
variable (B:ℝ)(M:ι→ℝ)(hB:0≤B)(hM:∀i∈s,0≤M i)
variable (hRb:∀z,|Rtest z|≤B)(hab:∀i∈s,∀z,|a i z|≤M i)
local notation "Rnative"=>NativeFirstScoreReserve.covariance P σ target (nativeCenter center) q
local notation "OldNative"=>NativeFirstScoreReserve.oldProfile P old
local notation "Weight"=>GaussianFixedFirstAverage.weight Rnative e w
local notation "Shift"=>GaussianFixedFirstAverage.shift shift

include hΛ hq hgap hTh hages hold holdb hsmall hw hwm hs hRoot ha hB hM hRb hab in
/-- Genuine whole-word three-leg FTC after reserving an independent
fixed native FIRST score. Every original old score and every full
profile baseline remains in the unchanged whole test. The additional
native fraction leaves the proved THREE-EIGHTHS elliptic floor. -/
def transfer :=
  ControlledJointWeightedWord.actual_joint_word_transfer P hΛ σ target center q hq hgap hTh hages u d Z D
    OldNative (NativeFirstScoreReserve.oldProfile_measurable P hold)
    (ε:=5*P.lower/8) (by linarith [P.lower_pos]) (NativeFirstScoreReserve.oldProfile_bounds P holdb)
    hsmall (μ.prod (multivariateGaussian 0 Rnative)) Weight
    (GaussianFixedFirstAverage.weight_integrable μ Rnative e hw)
    (GaussianFixedFirstAverage.weight_measurable Rnative e hwm)
    Shift (GaussianFixedFirstAverage.shift_measurable hs) s leaf Rtest a hRoot ha B M hB hM hRb hab
end SHE.NativeFirstScoreWordFTC
