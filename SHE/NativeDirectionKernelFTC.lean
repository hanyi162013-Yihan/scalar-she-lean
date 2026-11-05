module
public import SHE.NativeFirstScoreWordFTC
public import SHE.ControlledJointMarkedWord
public import SHE.NativeFirstScoreRepresentation
public import SHE.NativeFirstScoreReserve
public import SHE.GaussianFixedFirstAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeDirectionKernelFTC
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
variable (he:e ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
  (NativeFirstScoreReserve.covariance P σ target (nativeCenter center) q)).range)
local notation "Input"=>e
local notation "Weight"=>GaussianFixedFirstAverage.weight Rnative Input w
local notation "Shift"=>GaussianFixedFirstAverage.shift shift

local notation "A"=>ControlledFixedReserve.covariance P Λ u d OldNative σ target (nativeCenter center) q
local notation "Base"=>ControlledFiniteWord.baselines P Λ u d leaf
local notation "DBase"=>ControlledFiniteWord.baselineDerivatives P Λ u d leaf
local notation "Mean"=>ControlledJointWeightedWord.jointMeanVector σ target center q Λ Z D
local notation "Test"=>(fun θ:ℝ=>test s Rtest a (fun i=>Base i θ))

/-- The literal original Gaussian WHOLE-WORD kernel differentiated in
an arbitrary fixed native-reserve range direction, with every baseline intact. -/
def kernel (θ:ℝ):ℝ:=deriv (fun t:ℝ=>gaussianAverage
  (ControlledFixedReserve.covariance P Λ u d old σ target (nativeCenter center) q θ)
  (WeightedBorelAverage.average μ w shift (Test θ)) (Mean θ+t•Input)) 0

/-- The full genuine three-leg mark with the independent native first
score kept as part of the fixed OLD product weight. -/
def mark (θ:ℝ):ℝ:=WeightedWordMarking.mark s (μ.prod (multivariateGaussian 0 Rnative)) Weight Shift A Rtest a Base DBase
  (ControlledFixedReserve.mark P Λ u d OldNative σ target (nativeCenter center) q)
  (currentDirection target center q Z) (dampedDirection σ target center q Λ D) θ
local notation "Kernel"=>kernel (P:=P) (Λ:=Λ) (σ:=σ) (target:=target) (center:=center) (q:=q)
    (u:=u) (d:=d) (Z:=Z) (D:=D) (old:=old) (μ:=μ)
    (w:=w) (shift:=shift) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a)
    (e:=e)
local notation "Mark"=>mark (P:=P) (Λ:=Λ) (σ:=σ) (target:=target) (center:=center) (q:=q)
    (u:=u) (d:=d) (Z:=Z) (D:=D) (old:=old) (μ:=μ)
    (w:=w) (shift:=shift) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a)
    (e:=e)

include hq hgap hTh hages hold holdb hw hwm hs hRoot ha hB hM hRb hab he in
/-- Exact fixed-score representation of the ORIGINAL differentiated
whole-word kernel, with a three-eighths residual reserve. -/
theorem kernel_eq (θ:ℝ):Kernel θ=gaussianAverage (A θ)
    (WeightedBorelAverage.average (μ.prod (multivariateGaussian 0 Rnative)) Weight Shift (Test θ)) (Mean θ):=by
  let Bound:=B*∏i∈s,(M i+|Base i θ|)
  have hBound:0≤Bound:=mul_nonneg hB (Finset.prod_nonneg (fun i hi=>add_nonneg (hM i hi) (abs_nonneg _)))
  have ht:∀z,|Test θ z|≤Bound:=test_bound s Rtest a (fun i=>Base i θ) B M hB hM hRb hab
  exact NativeFirstScoreRepresentation.derivative P Λ u d old hold holdb σ target (nativeCenter center)
    (fun i=>hq.trans_lt (hgap i)) (fun i=>(hTh i).trans P.horizon_le_one) hages q hq θ Input he
    μ w hw hwm shift hs (Test θ) (measurable_test s Rtest a _ hRoot ha) Bound hBound ht (Mean θ)

include hΛ hq hgap hTh hages hold holdb hsmall hw hwm hs hRoot ha hB hM hRb hab he in
/-- Original two-clock native kernel endpoint difference equals its FULL
three-leg FTC. No signed-row term is substituted for this kernel change,
and no additional Gaussian or stochastic theorem is assumed. -/
theorem transfer:
    (∀ᵐθ∂volume,HasDerivAt Kernel (Mark θ) θ) ∧
      ∀r t,IntervalIntegrable Mark volume r t ∧ (∫θ in r..t,Mark θ)=Kernel t-Kernel r:=by
  have ht:=ControlledJointWeightedWord.actual_joint_marked_transfer P hΛ σ target center q hq hgap hTh hages u d Z D
    OldNative (NativeFirstScoreReserve.oldProfile_measurable P hold)
    (ε:=5*P.lower/8) (by linarith [P.lower_pos]) (NativeFirstScoreReserve.oldProfile_bounds P holdb)
    hsmall (μ.prod (multivariateGaussian 0 Rnative)) Weight
    (GaussianFixedFirstAverage.weight_integrable μ Rnative e hw)
    (GaussianFixedFirstAverage.weight_measurable Rnative e hwm)
    Shift (GaussianFixedFirstAverage.shift_measurable hs) s leaf Rtest a hRoot ha B M hB hM hRb hab
  have hkernel:Kernel=(fun θ=>gaussianAverage (A θ)
      (WeightedBorelAverage.average (μ.prod (multivariateGaussian 0 Rnative)) Weight Shift (Test θ)) (Mean θ)):=by
    funext θ
    exact kernel_eq
      (P:=P) (σ:=σ) (target:=target) (center:=center) (q:=q) (hq:=hq)
      (hgap:=hgap) (hTh:=hTh) (hages:=hages) (u:=u) (d:=d) (Z:=Z)
      (D:=D) (old:=old) (hold:=hold) (holdb:=holdb) (μ:=μ) (w:=w)
      (hw:=hw) (hwm:=hwm) (shift:=shift) (hs:=hs) (s:=s) (leaf:=leaf)
      (Rtest:=Rtest) (a:=a) (hRoot:=hRoot) (ha:=ha) (B:=B) (M:=M)
      (hB:=hB) (hM:=hM) (hRb:=hRb) (hab:=hab) (e:=e) (he:=he) θ
  rw [hkernel]
  exact ht
end SHE.NativeDirectionKernelFTC
