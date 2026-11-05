module
public import SHE.OrdinaryUncutPhysicalGradient
public import SHE.NativeJointColumnDirections
public import SHE.MixedUncutKernelPairing

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.OrdinaryUncutPhysicalColumns
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation WordRecursion OrthogonalItoChannels CutoffWordLevel CutoffWordHistories
  GaussianConvolution GaussianItoTest
open scoped NNReal ENNReal
local instance ordinaryUncutPhysicalColumns_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryUncutPhysicalColumns_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryUncutPhysicalColumns_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryUncutPhysicalColumns_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryUncutPhysicalColumns_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance ordinaryUncutPhysicalColumns_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryUncutPhysicalColumns_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryUncutPhysicalColumns_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryUncutPhysicalColumns_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)(k:ℕ)
local notation "NL"=>UncutWordEvaluation.normalizedLevel L k
local notation "Obs"=>(NL).observations.observations
local notation "Term"=>(NL).terminal
local notation "Raw"=>OrdinaryUncutPhysicalGradient.raw m L k
local notation "Mean"=>OrdinaryPhysicalGradient.mean m NL

/-- Every coordinate is the FULL Gaussian-word derivative, with the
normalization restored once and the actual ordinary-U mean retained. -/
theorem action(ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:History Y k×(ℝ≥0×Ω))
    (hq:R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<Term z.1):
    ℓ (Raw z)=fderiv ℝ (gaussianAverage (covariance R.reference (Obs z.1)
      (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)) (Mean z)
      (WithLp.toLp 2 (fun i:Fin (n+k)=>ℓ (OrdinaryPhysicalGradient.row m (Obs z.1) z.2 i))):=by
  let w:=UncutSmoothWords.weight L k z.1
  have ha:gaussianAverage (covariance R.reference (Obs z.1) (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)=
      w • backward ((NL).window z.1) ((NL).test z.1) (z.2.1:ℝ):=by
    rw [UncutSmoothWords.test_eq_weight_normalized]
    change GaussianSmooth.average _ (w • (NL).test z.1)=_
    rw [NormalizedInsertion.average_smul]
    congr 1
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (covariance R.reference (Obs z.1) (z.2.1:ℝ) (Term z.1))) _ =
      GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (covariance R.reference (Obs z.1) (ClippedCovariance.clip R.base (Term z.1) (z.2.1:ℝ)) (Term z.1))) _
    rw [ClippedCovariance.clip_eq ⟨hq.1.le,hq.2.le⟩]
  rw [ha,fderiv_const_smul_field]
  rw [OrdinaryUncutPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,if_pos hq,map_smul,map_sum]
  rw [FiniteItoGradientAction.coordinates]
  simp only [ContinuousLinearMap.smul_apply,Pi.smul_apply,map_smul,smul_eq_mul,WithLp.ofLp_toLp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The pure-U original additive and residual coordinates are exact
native L2 pairings with their respective same-Haar columns. -/
theorem channels(z:History Y k×(ℝ≥0×Ω))
    (hq:R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<Term z.1)
    (hT:∀i,(z.2.1:ℝ)<(Obs z.1 i).target)(j:HaarNode):
    let D:=fderiv ℝ (gaussianAverage (covariance R.reference (Obs z.1)
      (z.2.1:ℝ) (Term z.1)) (UncutSmoothWords.test L k z.1)) (Mean z)
    NativeJointColumnDirections.left j (Raw z)=
      (FiniteHeatRows.functional D (Obs z.1) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ m.additive_pos).1))).re∧
    NativeJointColumnDirections.right j (Raw z)=
      (FiniteHeatRows.functional D (Obs z.1) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j (m.coefficient z.2).1))).re:=by
  intro D
  have hd {l W:ℝ}(hl:0<l)(f:EllipticField l W):
      WithLp.toLp 2 (fun i:Fin (n+k)=>NativeObservationCovariance.row hl f
        (Obs z.1 i).target (z.2.1:ℝ) (Obs z.1 i).center j)=
      PhysicalMeanRange.currentDirection (fun i=>(Obs z.1 i).target)
        (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) (z.2.1:ℝ)
        (CircleNormalization.push (globalHaarColumn j f.1)):=by
    apply PiLp.ext
    intro i
    change NativeObservationCovariance.row hl f (Obs z.1 i).target (z.2.1:ℝ) (Obs z.1 i).center j=_
    rw [NativeObservationColumnMean.row hl f (hT i)]
    change PhysicalProfile.physicalHeatMean _ (_,_) = PhysicalProfile.physicalHeatMean _ (_,_)
    have hc:StoppedGaussianScore.nativeCenter
        (fun i=>NativeHeatSpan.unitCenter (Obs z.1 i).center) i=(Obs z.1 i).center:=
      NativeHeatSpan.scale_inverse _
    rw [hc]
  constructor
  · rw [action m L k _ z hq]
    change D (WithLp.toLp 2 (fun i:Fin (n+k)=>NativeObservationCovariance.row m.additive_pos
      (AdditiveHaarForcing.constantField κ m.additive_pos) (Obs z.1 i).target (z.2.1:ℝ) (Obs z.1 i).center j))=_
    rw [hd]
    exact MixedUncutKernelPairing.functional_current _ _ _ hT _
  · rw [action m L k _ z hq]
    change D (WithLp.toLp 2 (fun i:Fin (n+k)=>NativeObservationCovariance.row m.lower_pos
      (m.coefficient z.2) (Obs z.1 i).target (z.2.1:ℝ) (Obs z.1 i).center j))=_
    rw [hd]
    exact MixedUncutKernelPairing.functional_current _ _ _ hT _

end SHE.OrdinaryUncutPhysicalColumns
