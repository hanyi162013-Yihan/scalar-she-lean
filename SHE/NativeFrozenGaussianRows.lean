module
public import SHE.DeterministicNativeHeatRows
public import SHE.ControlledResidualContinuity
public import SHE.NativeRowFieldContinuity
public import SHE.FrozenReferenceFields
public import SHE.AdditiveHaarForcing
public import SHE.PastFrozenPrefixRows
public import SHE.SingularInputBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeFrozenGaussianRows
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open NativeObservationCovariance NativeObservationEndpoint OrthogonalItoChannels PredictableItoRotation
open ControlledProfile
open scoped NNReal ENNReal
local instance unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H v b:ℝ≥0)
variable (P:CanonicalCovariance.ProfileParameters) (Λ κ:ℝ) (hκ:0<κ) (hκP:κ<P.lower)

def timeField (ξ:ℝ) (p:Inputs) (q:ℝ≥0):EllipticField (P.lower-κ) (P.upper-κ):=
  ControlledResidualField.field P Λ κ hκP ((p,ξ),(q:ℝ)-(v:ℝ))

theorem timeField_measurable (ξ:ℝ) (p:Inputs):Measurable (timeField v P Λ κ hκP ξ p):=
  (ControlledResidualField.field_measurable P Λ κ hκP).comp
    ((measurable_const (a:=(p,ξ))).prodMk (measurable_coe_nnreal_real.sub_const (v:ℝ)))

def lift (side:Bool):RealHaarInput→ₗᵢ[ℝ]Both RealHaarInput:=if side then right else left

def mapRow (side:Bool) (R:Process (E:=RealHaarInput) 𝓕 μ H):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  processIsometry 𝓕 μ H (fun _=>lift side)
    ((lift side).continuous.measurable.comp measurable_snd) R

theorem mapRow_ae (side:Bool) (R:Process (E:=RealHaarInput) 𝓕 μ H):
    mapRow 𝓕 μ H side R=ᵐ[energyMeasure μ H] fun p=>lift side (R p):=
  processIsometry_ae 𝓕 μ H _ _ R

def additive (x:HeatCircle) (hbH:b≤H):Process (E:=RealHaarInput) 𝓕 μ H:=
  DeterministicNativeHeatRows.process 𝓕 μ H b hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) measurable_const le_rfl x hbH

def residual (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data) (ξ:ℝ) (x:HeatCircle) (hbH:b≤H):
    Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
    (FrozenReferenceFields.field P Λ κ ξ hκP v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ ξ hκP v data hdata) le_rfl x hbH

variable{n:ℕ}(side:Fin n→Bool) (ξ:Fin n→ℝ) (center:Fin n→HeatCircle)

def rows (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data) (hbH:b≤H) (i:Fin n):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  if side i then mapRow 𝓕 μ H true (residual 𝓕 μ H v b P Λ κ hκP data hdata (ξ i) (center i) hbH)
  else mapRow 𝓕 μ H false (additive 𝓕 μ H b κ hκ (center i) hbH)

def raw (p:Inputs) (i:Fin n) (t:ℝ):Both RealHaarInput:=
  if side i then lift true (DeterministicNativeHeatRows.raw (T:=(b:ℝ)) b (sub_pos.mpr hκP)
    (timeField v P Λ κ hκP (ξ i) p) (center i) t)
  else lift false (DeterministicNativeHeatRows.raw (T:=(b:ℝ)) b hκ
    (fun _=>AdditiveHaarForcing.constantField κ hκ) (center i) t)

include 𝓕 μ in
theorem raw_measurable (p:Inputs) (i:Fin n):Measurable (raw v b P Λ κ hκ hκP side ξ center p i):=by
  unfold raw
  split_ifs
  · exact (lift true).continuous.measurable.comp
      (DeterministicNativeHeatRows.raw_measurable (T:=(b:ℝ)) 𝓕 μ b (sub_pos.mpr hκP) _
        (timeField_measurable v P Λ κ hκP (ξ i) p) (center i))
  · exact (lift false).continuous.measurable.comp
      (DeterministicNativeHeatRows.raw_measurable (T:=(b:ℝ)) 𝓕 μ b hκ _ measurable_const (center i))

include 𝓕 μ in
theorem raw_square_integrable (hvb:v≤b) (p:Inputs) (i:Fin n):
    IntervalIntegrable (fun t=>‖raw v b P Λ κ hκ hκP side ξ center p i t‖^2) volume (v:ℝ) b:=by
  unfold raw
  split_ifs
  · simpa only [LinearIsometry.norm_map] using
      DeterministicNativeHeatRows.square_integrable (T:=(b:ℝ)) 𝓕 μ b (sub_pos.mpr hκP)
        (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) _
        (timeField_measurable v P Λ κ hκP (ξ i) p) le_rfl (center i) v hvb
  · simpa only [LinearIsometry.norm_map] using
      DeterministicNativeHeatRows.square_integrable (T:=(b:ℝ)) 𝓕 μ b hκ hκ.le _ measurable_const le_rfl (center i) v hvb

variable (hΛ:0≤Λ) (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hΛ hsmall in
theorem raw_parameter_continuous (i:Fin n) (t:ℝ):
    Continuous (fun p:Inputs=>raw v b P Λ κ hκ hκP side ξ center p i t):=by
  unfold raw DeterministicNativeHeatRows.raw
  split_ifs with hi hb
  · exact (lift true).continuous.comp
      ((NativeRowFieldContinuity.row (sub_pos.mpr hκP) hb (center i)).comp
        (ControlledResidualContinuity.field P hΛ κ (ξ i) hκP hsmall ((t.toNNReal:ℝ)-(v:ℝ))))
  all_goals exact continuous_const

include 𝓕 μ hΛ hsmall in
theorem raw_joint_measurable (i:Fin n):
    Measurable (fun z:Inputs×ℝ=>raw v b P Λ κ hκ hκP side ξ center z.1 i z.2):=by
  exact measurable_uncurry_of_continuous_of_measurable
    (raw_parameter_continuous v b P Λ κ hκ hκP side ξ center hΛ hsmall i)
    (fun p=>raw_measurable 𝓕 μ v b P Λ κ hκ hκP side ξ center p i)

theorem rows_ae (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data) (hbH:b≤H) (i:Fin n):
    ∀ᵐz∂energyMeasure μ H,v<z.1 ∧ z.1<b→
      rows 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH i z=
        raw v b P Λ κ hκ hκP side ξ center (data z.2) i (z.1:ℝ):=by
  by_cases hi:side i
  · have hl:=mapRow_ae 𝓕 μ H true
      (residual 𝓕 μ H v b P Λ κ hκP data hdata (ξ i) (center i) hbH)
    have hr:=FullHorizonEndpoint.process_ae 𝓕 μ H b (sub_pos.mpr hκP)
      (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
      (FrozenReferenceFields.field P Λ κ (ξ i) hκP v data)
      (FrozenReferenceFields.field_predictable 𝓕 P Λ κ (ξ i) hκP v data hdata) le_rfl (center i) hbH
    filter_upwards [hl,hr] with z hl hr hz
    have hzb:(z.1:ℝ)<(b:ℝ):=by exact_mod_cast hz.2
    have hf:FrozenReferenceFields.field P Λ κ (ξ i) hκP v data z=
        timeField v P Λ κ hκP (ξ i) (data z.2) z.1:=by
      unfold FrozenReferenceFields.field timeField
      rw [PredictablePastParameter.held_eq data (0,0) hz.1]
    simp only [rows,ite_eq_left hi] at ⊢
    rw [hl]
    change lift true (FullHorizonEndpoint.process 𝓕 μ H b (sub_pos.mpr hκP) _ _ _ le_rfl (center i) hbH z)=_
    rw [hr]
    simp only [raw,ite_eq_left hi,DeterministicNativeHeatRows.raw,Real.toNNReal_coe,
      FullHorizonEndpoint.raw,indicator_apply,StoppedItoInputs.before,mem_ofPred_eq,
      ite_eq_left hzb,fullIntegrand,hf]
  · have hl:=mapRow_ae 𝓕 μ H false (additive 𝓕 μ H b κ hκ (center i) hbH)
    have hr:=DeterministicNativeHeatRows.process_ae 𝓕 μ H b hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) measurable_const le_rfl (center i) hbH
    filter_upwards [hl,hr] with z hl hr hz
    simp only [rows,ite_eq_right hi] at ⊢
    rw [hl]
    change lift false (DeterministicNativeHeatRows.process 𝓕 μ H b hκ hκ.le _ measurable_const le_rfl (center i) hbH z)=_
    rw [hr]
    simp only [raw,ite_eq_right hi]

def cap:ℝ:=P.upper*(1+heatConstant)

theorem cap_nonneg:0≤cap P:=mul_nonneg P.upper_nonneg (by linarith [heatConstant_pos])

theorem bound (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data) (hbH:b≤H) (hb1:(b:ℝ)≤1) (i:Fin n):
    SingularInputBounds.Bound 𝓕 μ H b (cap P)
      (rows 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH i):=by
  have hC:0≤1+heatConstant:=by linarith [heatConstant_pos]
  have hκU:κ≤P.upper:=hκP.le.trans ((P.lower_bound 0).trans (P.upper_bound 0))
  by_cases hi:side i
  · have hl:=mapRow_ae 𝓕 μ H true
      (residual 𝓕 μ H v b P Λ κ hκP data hdata (ξ i) (center i) hbH)
    have hr:=FullHorizonEndpointVersion.singular_bound 𝓕 μ H b (sub_pos.mpr hκP)
      (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
      (FrozenReferenceFields.field P Λ κ (ξ i) hκP v data)
      (FrozenReferenceFields.field_predictable 𝓕 P Λ κ (ξ i) hκP v data hdata) le_rfl (center i) hbH hb1
    filter_upwards [hl,hr] with z hl hr hz
    simp only [rows,ite_eq_left hi]
    rw [hl,LinearIsometry.norm_map]
    exact (hr hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sub_le_self P.upper hκ.le) hC)
      (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hz)) _))
  · have hl:=mapRow_ae 𝓕 μ H false (additive 𝓕 μ H b κ hκ (center i) hbH)
    have hr:=DeterministicNativeHeatRows.bound 𝓕 μ H b hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) measurable_const le_rfl (center i) hbH hb1
    filter_upwards [hl,hr] with z hl hr hz
    simp only [rows,ite_eq_right hi]
    rw [hl,LinearIsometry.norm_map]
    exact (hr hz).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκU hC)
      (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hz)) _))

theorem raw_bound (p:Inputs) (i:Fin n) {t:ℝ} (ht0:0≤t) (htb:t<(b:ℝ)):
    ‖raw v b P Λ κ hκ hκP side ξ center p i t‖^2≤
      P.upper*(1+heatConstant*((b:ℝ)-t)^(-(1/2:ℝ))):=by
  have hC:0≤1+heatConstant*((b:ℝ)-t)^(-(1/2:ℝ)):=by positivity [heatConstant_pos]
  have hκU:κ≤P.upper:=hκP.le.trans ((P.lower_bound 0).trans (P.upper_bound 0))
  unfold raw DeterministicNativeHeatRows.raw
  simp only [Real.coe_toNNReal t ht0,ite_eq_left htb]
  by_cases hi:side i
  · simp only [ite_eq_left hi,LinearIsometry.norm_map]
    exact (NativeObservationProcess.row_norm_sq_bound (sub_pos.mpr hκP)
      (timeField v P Λ κ hκP (ξ i) p t.toNNReal) htb le_rfl (center i)).trans
        (mul_le_mul_of_nonneg_right (sub_le_self P.upper hκ.le) hC)
  · simp only [ite_eq_right hi,LinearIsometry.norm_map]
    exact (NativeObservationProcess.row_norm_sq_bound hκ
      (AdditiveHaarForcing.constantField κ hκ) htb le_rfl (center i)).trans
        (mul_le_mul_of_nonneg_right hκU hC)

end SHE.NativeFrozenGaussianRows
