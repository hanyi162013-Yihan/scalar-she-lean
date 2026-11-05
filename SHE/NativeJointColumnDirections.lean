module
public import SHE.NativeObservationColumnMean
public import SHE.FiniteItoGradientAction
public import SHE.MixedNativeJointPhysical
public import SHE.NativeHeatSpan
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeJointColumnDirections
open MeasureTheory FiniteHaar StoppedFourier PhysicalMeanRange StoppedGaussianScore
  OrthogonalItoChannels GaussianIncrement
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

def left (k:HaarNode):Both RealHaarInput→L[ℝ]ℝ:=
  (lp.evalCLM ℝ (fun _:HaarNode=>ℝ) 2 k).comp (WithLp.fstL 2 ℝ RealHaarInput RealHaarInput)

def right (k:HaarNode):Both RealHaarInput→L[ℝ]ℝ:=
  (lp.evalCLM ℝ (fun _:HaarNode=>ℝ) 2 k).comp (WithLp.sndL 2 ℝ RealHaarInput RealHaarInput)

variable {n:ℕ}{ell M κ:ℝ}(hell:0<ell)(hκ:0<κ)
variable (cU cV:EllipticField ell M)(σ target:Fin n→ℝ)(center:Fin n→UnitAddCircle)(q Λ:ℝ)

def physical (i:Fin n):Both RealHaarInput:=WithLp.toLp 2
  (NativeObservationCovariance.row hκ (AdditiveHaarForcing.constantField κ hκ)
    (target i) q (nativeCenter center i),
   NativeObservationCovariance.row hell cV (target i) q (nativeCenter center i)+
     (1-Real.exp (-Λ*(σ i-q))) •
       (NativeObservationCovariance.row hell cU (target i) q (nativeCenter center i)-
        NativeObservationCovariance.row hell cV (target i) q (nativeCenter center i)))

/-- The common additive input uses the SAME actual Haar column. -/
theorem left_direction (hq:∀i,q<target i)(k:HaarNode):
    WithLp.toLp 2 (fun i=>left k (physical hell hκ cU cV σ target center q Λ i))=
      currentDirection target center q
        (CircleNormalization.push (globalHaarColumn k (AdditiveHaarForcing.constantField κ hκ).1)):=by
  change WithLp.toLp 2 (fun i=>NativeObservationCovariance.row hκ
    (AdditiveHaarForcing.constantField κ hκ) (target i) q (nativeCenter center i) k)=_
  exact NativeObservationColumnMean.direction hκ _ target center q hq k

/-- The actual joint residual input splits into the undamped U column
and the stopped damped V-minus-U column, with its original stop ages. -/
theorem right_direction (hq:∀i,q<target i)(k:HaarNode):
    WithLp.toLp 2 (fun i=>right k (physical hell hκ cU cV σ target center q Λ i))=
      currentDirection target center q (CircleNormalization.push (globalHaarColumn k cU.1))+
        dampedDirection σ target center q Λ
          (CircleNormalization.push (globalHaarColumn k cV.1)-
           CircleNormalization.push (globalHaarColumn k cU.1)):=by
  apply PiLp.ext
  intro i
  change (NativeObservationCovariance.row hell cV (target i) q (nativeCenter center i) k)+
    (1-Real.exp (-Λ*(σ i-q)))*
      (NativeObservationCovariance.row hell cU (target i) q (nativeCenter center i) k-
       NativeObservationCovariance.row hell cV (target i) q (nativeCenter center i) k)=_
  rw [NativeObservationColumnMean.row hell cV (hq i),
    NativeObservationColumnMean.row hell cU (hq i)]
  change _=PhysicalProfile.physicalHeatMean _ (target i-q,nativeCenter center i)+
    Real.exp (-Λ*(σ i-q))*PhysicalProfile.physicalHeatMean _ (target i-q,nativeCenter center i)
  rw [←PhysicalProfile.physicalHeatMean_difference (sub_pos.mpr (hq i))]
  ring

end SHE.NativeJointColumnDirections
