module
public import SHE.NativeJointGradientClock
public import SHE.NativeJointGammaFields
public import SHE.NativeRowProductEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeJointRowClock
open Set MeasureTheory PredictableL2 Real AddCircle StoppedFourier NativeHeatObservation NativeMovingCurrentGamma ScalarGaussianSemigroup DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointRowClock_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeJointRowClock_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeJointRowClock_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeJointRowClock_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeJointRowClock_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeJointRowClock_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeJointRowClock_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeJointRowClock_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]

def variance (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2) (Λ:ℝ) (v b:ℝ≥0):
    (ℝ≥0×Ω)×HeatCircle→ℝ:=
  NativeCanonicalVarianceField.field P Λ 0 v b (fun ω=>U (v,ω)) (fun ω=>V (v,ω)-U (v,ω))
def mean (U V:ℝ≥0×Ω→RealL2) (Λ θ:ℝ) (v b:ℝ≥0):(ℝ≥0×Ω)×HeatCircle→ℝ:=
  PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ θ b)
def field (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2) (Λ:ℝ) (v b:ℝ≥0)
    (a:ℝ→ℝ) (j:ℕ) (θ:ℝ): (ℝ≥0×Ω)×HeatCircle→ℂ:=
  ScalarHeatSingleMultiplier.field a j (variance P U V Λ v b) (mean U V Λ θ v b)

/-- Both original current multipliers are genuinely jointly Borel;
only ordinary predictability of the two physical state processes is used. -/
theorem field_measurable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (Λ:ℝ) (v b:ℝ≥0) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) (j:ℕ) (θ:ℝ):
    Measurable (field P U V Λ v b a j θ):=by
  have hs:=NativeJointGammaFields.variance_predictable (𝓕:=𝓕) (v:=v) (b:=b)
    (U:=U) (V:=V) (hU:=hU) (hV:=hV) (P:=P) (Λ:=Λ) 0
  have hx:=NativeJointGammaFields.current_predictable (𝓕:=𝓕) (v:=v) (b:=b)
    (U:=U) (V:=V) (hU:=hU) (hV:=hV) (Λ:=Λ) θ
  have hid:@Measurable (ℝ≥0×Ω) (ℝ≥0×Ω) inferInstance 𝓕.predictable id:=
    measurable_id'' (predictable_le_product 𝓕)
  exact ScalarHeatSingleMultiplier.field_measurable ha j
    (hs.comp (hid.prodMap measurable_id)) (hx.comp (hid.prodMap measurable_id))

def directGradient (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (Λ:ℝ) (H:ℝ≥0) (a:ℝ→ℝ) (j:ℕ) (v h τ:ℝ) (z:Ω×HeatCircle):ℝ:=
  let Ur:=fun p:ℝ×Ω=>U (p.1.toNNReal,p.2)
  let Dr:=NativePathZeroExtension.extend H (fun p=>V p-U p)
  let σ:=NativeMovingCurrentGamma.variance P Ur Dr Λ h 0 (τ,((v,z.1),z.2))
  let x:=current Ur h (τ,((v,z.1),z.2))
  let y:=x+NativeMovingJointGamma.direction Dr Λ h (τ,((v,z.1),z.2))
  deriv (heat σ.toNNReal (ScalarHeatBands.band a (j+1))) y-
    deriv (heat σ.toNNReal (ScalarHeatBands.band a (j+1))) x

/-- Exact original-sample energy of the actual current native rows,
identified with the jointly Borel moving-current gradient integrand.
This discharges the root/clock normalization in the six-slot bound. -/
theorem energy_eq (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (U V:ℝ≥0×Ω→RealL2)
    (hU:StronglyMeasurable[𝓕.predictable] U) (hV:StronglyMeasurable[𝓕.predictable] V)
    (Λ:ℝ) (H:ℝ≥0) {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) {A:ℝ} (hA:0≤A)
    (hh:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ)
    {v h τ:ℝ} (hv:0<v) (hvh:v+h≤H) (hτ:τ∈Ioo (0:ℝ) h):
    (∫ω,‖NativeRandomRows.nativeRow (field P U V Λ v.toNNReal (v+h).toNNReal a j 0) ((v+h-τ).toNNReal,ω)-
      NativeRandomRows.nativeRow (field P U V Λ v.toNNReal (v+h).toNNReal a j 1) ((v+h-τ).toNNReal,ω)‖^2 ∂μ)=
    ∫z:Ω×HeatCircle,|directGradient P U V Λ H a j v h τ z|^2 ∂μ.prod haarAddCircle:=by
  let F0:=field P U V Λ v.toNNReal (v+h).toNNReal a j 0
  let F1:=field P U V Λ v.toNNReal (v+h).toNNReal a j 1
  have hm0:=field_measurable 𝓕 P U V hU hV Λ v.toNNReal (v+h).toNNReal ha j 0
  have hm1:=field_measurable 𝓕 P U V hU hV Λ v.toNNReal (v+h).toNNReal ha j 1
  have hb0:=ScalarHeatSingleMultiplier.field_bound ha hA P.exponent_pos.le P.exponent_le_one hh j
    (variance P U V Λ v.toNNReal (v+h).toNNReal) (mean U V Λ 0 v.toNNReal (v+h).toNNReal)
  have hb1:=ScalarHeatSingleMultiplier.field_bound ha hA P.exponent_pos.le P.exponent_le_one hh j
    (variance P U V Λ v.toNNReal (v+h).toNNReal) (mean U V Λ 1 v.toNNReal (v+h).toNNReal)
  have he:=NativeRowProductEnergy.difference μ F0 F1 hm0 hm1 hb0 hb1 (v+h-τ).toNNReal
  rw [he.2]
  have hUr:Measurable (fun z:ℝ×Ω=>U (z.1.toNNReal,z.2)):=
    hU.measurable.mono (predictable_le_product 𝓕) le_rfl |>.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hVr:Measurable (fun z:ℝ×Ω=>V (z.1.toNNReal,z.2)):=
    hV.measurable.mono (predictable_le_product 𝓕) le_rfl |>.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hD:Measurable (NativePathZeroExtension.extend H (fun p=>V p-U p)):=
    NativePathZeroExtension.measurable H (fun p=>V p-U p)
      ((hV.measurable.mono (predictable_le_product 𝓕) le_rfl).sub
        (hU.measurable.mono (predictable_le_product 𝓕) le_rfl))
  have hmap:Measurable (fun z:Ω×HeatCircle=>(τ,((v,z.1),z.2))):=
    measurable_const.prodMk ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hs:= (NativeMovingCurrentGamma.variance_measurable P _ _ hUr hD Λ h 0).comp hmap
  have hx:= (NativeMovingCurrentGamma.current_measurable _ hUr h).comp hmap
  have hy:= hx.add ((NativeMovingJointGamma.direction_measurable _ hD Λ h).comp hmap)
  have hg0:Measurable (directGradient P U V Λ H a j v h τ):=
    (PolynomialGaussianDecay.derivative_measurable ha (j+1) _ _ hs hy).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) _ _ hs hx)
  have hg:Measurable (fun z:Ω×HeatCircle=>|directGradient P U V Λ H a j v h τ z|^2):=by
    simpa only [Real.norm_eq_abs] using hg0.norm.pow_const 2
  have hm:Measurable (fun z:Ω×HeatCircle=>‖F0 (((v+h-τ).toNNReal,z.1),z.2)-F1 (((v+h-τ).toNNReal,z.1),z.2)‖^2):=
    (((hm0.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).sub
      (hm1.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))).norm).pow_const 2
  apply integral_congr_ae
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm hg)).mpr
  apply ae_of_all
  intro ω
  refine (NativeJointGradientClock.gradient_ae P U V Λ H a j hv hvh hτ ω).mono (fun x hx=>?_)
  simpa only [F0,F1,field,variance,mean,ScalarHeatSingleMultiplier.field,
    ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,directGradient] using hx
end SHE.NativeJointRowClock
