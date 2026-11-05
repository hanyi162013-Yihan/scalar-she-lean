module
public import SHE.NativeFirstScoreKernelFTC
public import SHE.WeightedAverageDifferentiable
public import SHE.FiniteCenteredSmooth
public import SHE.MixedJointGradientDerivatives
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
namespace SHE.NativeFirstScoreNoiseComparison
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
variable (f:CircleL2)
local notation "Input"=>currentDirection target center q f
local notation "Weight"=>GaussianFixedFirstAverage.weight Rnative Input w
local notation "Shift"=>GaussianFixedFirstAverage.shift shift

local notation "A"=>ControlledFixedReserve.covariance P Λ u d OldNative σ target (nativeCenter center) q
local notation "Base"=>ControlledFiniteWord.baselines P Λ u d leaf
local notation "DBase"=>ControlledFiniteWord.baselineDerivatives P Λ u d leaf
local notation "Mean"=>ControlledJointWeightedWord.jointMeanVector σ target center q Λ Z D
local notation "Test"=>(fun θ:ℝ=>test s Rtest a (fun i=>Base i θ))

local notation "Kernel"=>NativeFirstScoreKernelFTC.kernel (P:=P) (Λ:=Λ) (σ:=σ) (target:=target) (center:=center) (q:=q)
    (u:=u) (d:=d) (Z:=Z) (D:=D) (old:=old) (μ:=μ)
    (w:=w) (shift:=shift) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a)
    (f:=f)
local notation "Mark"=>NativeFirstScoreKernelFTC.mark (P:=P) (Λ:=Λ) (σ:=σ) (target:=target) (center:=center) (q:=q)
    (u:=u) (d:=d) (Z:=Z) (D:=D) (old:=old) (μ:=μ)
    (w:=w) (shift:=shift) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a)
    (f:=f)

def whole (θ:ℝ):State n→ℝ:=gaussianAverage
  (ControlledFixedReserve.covariance P Λ u d old σ target (nativeCenter center) q θ)
  (WeightedBorelAverage.average μ w shift (Test θ))
local notation "Whole"=>(fun θ:ℝ=>whole (P:=P) (Λ:=Λ) (σ:=σ) (target:=target)
  (center:=center) (q:=q) (u:=u) (d:=d) (old:=old) (μ:=μ) (w:=w)
  (shift:=shift) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a) θ)

variable (g:CircleL2)
local notation "E"=>dampedDirection σ target center q Λ g

def fullColumn (θ:ℝ):ℝ:=deriv (fun t:ℝ=>Whole θ (Mean θ+t•(Input+θ•E))) 0
local notation "Column"=>(fun θ:ℝ=>fullColumn (P:=P) (Λ:=Λ) (σ:=σ) (target:=target)
  (center:=center) (q:=q) (u:=u) (d:=d) (Z:=Z) (D:=D) (old:=old) (μ:=μ)
  (w:=w) (shift:=shift) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a) (f:=f) (g:=g) θ)

variable (hRs:SmoothCylinders.BoundedSmooth Rtest)
variable (has:∀i∈s,SmoothCylinders.BoundedSmooth (a i))

include hw hwm hs hRs has in
/-- Actual bounded-smooth root and leaves discharge whole-kernel
Frechet differentiability, including the signed old score average. -/
theorem whole_differentiable (θ:ℝ):Differentiable ℝ (Whole θ):=by
  exact WeightedAverageDifferentiable.gaussian_differentiable μ w hw hwm shift hs _ _
    (FiniteCenteredSmooth.test s Rtest a (fun i=>Base i θ) hRs has)

include hw hwm hs hRs has in
/-- The literal full joint column difference contains BOTH the native
kernel change and the signed stop-weighted residual-difference column. -/
theorem split:
    Column 1-Column 0=Kernel 1-Kernel 0+
      deriv (fun t:ℝ=>Whole 1 (Mean 1+t•E)) 0:=by
  have hD:=whole_differentiable (P:=P) (Λ:=Λ) (σ:=σ) (target:=target) (center:=center)
    (q:=q) (u:=u) (d:=d) (old:=old) (μ:=μ) (w:=w) (hw:=hw) (hwm:=hwm)
    (shift:=shift) (hs:=hs) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a) (hRs:=hRs) (has:=has) 1
  have hOne:Column 1=Kernel 1+deriv (fun t:ℝ=>Whole 1 (Mean 1+t•E)) 0:=by
    change deriv (fun t:ℝ=>Whole 1 (Mean 1+t•(Input+(1:ℝ)•E))) 0=_
    rw [one_smul,←MixedJointGradientDerivatives.scalar_deriv _ _ _ (hD (Mean 1)),map_add]
    rw [MixedJointGradientDerivatives.scalar_deriv _ _ _ (hD (Mean 1)),
      MixedJointGradientDerivatives.scalar_deriv _ _ _ (hD (Mean 1))]
    rfl
  have hZero:Column 0=Kernel 0:=by
    simp only [fullColumn,zero_smul,add_zero]
    rfl
  rw [hOne,hZero]
  ring

include hΛ hq hgap hTh hages hold holdb hsmall hw hwm hs hRoot ha hB hM hRb hab hRs has in
/-- COMPLETE qualitative higher-noise identity: the original full
joint column difference is the three-leg whole-kernel FTC PLUS the
signed damped column. All actual baseline derivatives are retained. -/
theorem comparison:
    IntervalIntegrable Mark volume 0 1 ∧
    Column 1-Column 0=(∫θ in (0:ℝ)..1,Mark θ)+
      deriv (fun t:ℝ=>Whole 1 (Mean 1+t•E)) 0:=by
  have ht:=NativeFirstScoreKernelFTC.transfer
    (P:=P) (hΛ:=hΛ) (σ:=σ) (target:=target) (center:=center) (q:=q)
    (hq:=hq) (hgap:=hgap) (hTh:=hTh) (hages:=hages) (u:=u) (d:=d)
    (Z:=Z) (D:=D) (old:=old) (hold:=hold) (holdb:=holdb) (hsmall:=hsmall)
    (μ:=μ) (w:=w) (hw:=hw) (hwm:=hwm) (shift:=shift) (hs:=hs)
    (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a) (hRoot:=hRoot) (ha:=ha)
    (B:=B) (M:=M) (hB:=hB) (hM:=hM) (hRb:=hRb) (hab:=hab) (f:=f)
  refine ⟨(ht.2 0 1).1,?_⟩
  rw [(ht.2 0 1).2]
  exact split (P:=P) (Λ:=Λ) (σ:=σ) (target:=target) (center:=center) (q:=q)
    (u:=u) (d:=d) (Z:=Z) (D:=D) (old:=old) (μ:=μ) (w:=w) (hw:=hw) (hwm:=hwm)
    (shift:=shift) (hs:=hs) (s:=s) (leaf:=leaf) (Rtest:=Rtest) (a:=a)
    (f:=f) (g:=g) (hRs:=hRs) (has:=has)
end SHE.NativeFirstScoreNoiseComparison
