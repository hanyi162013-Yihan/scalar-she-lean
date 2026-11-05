module

public import SHE.HilbertColumns
public import SHE.NativeRepresentativeEnergy
public import SHE.SectionEnergy
public import SHE.PhysicalProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.NativeCurrentSourceEnergy
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatObservation DyadicApproximation FiniteHaar ProfileL2
local instance nativeCurrentSourceEnergy_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeCurrentSourceEnergy_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCurrentSourceEnergy_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCurrentSourceEnergy_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeCurrentSourceEnergy_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeCurrentSourceEnergy_circleSecond : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance nativeCurrentSourceEnergy_unitPositive : Fact (0<(1:ℝ)):=⟨by norm_num⟩
local instance nativeCurrentSourceEnergy_unitSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeCurrentSourceEnergy_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]
open Classical

/-- The true current input after any positive heat age; at zero age we
keep the ORIGINAL native scalar representatives. -/
def value (U V:Ω→RealL2) (τ:ℝ) (y:Ω×HeatCircle):ℝ:=
  if 0<τ then PhysicalProfile.physicalHeatMean (embed (V y.1-U y.1)) (τ,y.2)
  else PredictableScalarField.nativeField V y-PredictableScalarField.nativeField U y

theorem value_measurable (U V:Ω→RealL2) (hU:Measurable U) (hV:Measurable V) (τ:ℝ):
    Measurable (value U V τ):=by
  by_cases hτ:0<τ
  · have hp:Measurable (fun y:Ω×HeatCircle=>(embed (V y.1-U y.1),(τ,y.2))):=
      ((embed.continuous.measurable.comp (hV.sub hU)).comp measurable_fst).prodMk
        ((measurable_const (a:=τ)).prodMk measurable_snd)
    convert! PhysicalProfile.physicalHeatMean_joint_measurable.comp hp using 1
    funext y
    simp only [value,if_pos hτ,Function.comp_def]
  · convert! (PredictableScalarField.nativeField_measurable hV).sub
      (PredictableScalarField.nativeField_measurable hU) using 1
    funext y
    simp only [value,if_neg hτ,Pi.sub_apply]

/-- Positive heat smoothing and the genuine newest point both preserve
the TRUE Hilbert input energy. In particular there is no pointwise heat
singularity in the distinguished current factor. -/
theorem product_energy (μ:Measure Ω) [SFinite μ]
    (U V:Ω→RealL2) (hU:Measurable U) (hV:Measurable V)
    (hdi:Integrable (fun ω=>‖V ω-U ω‖^2) μ) (τ:ℝ):
    Integrable (fun y=>value U V τ y^2) (μ.prod haarAddCircle) ∧
      (∫y,value U V τ y^2 ∂μ.prod haarAddCircle)≤∫ω,‖V ω-U ω‖^2 ∂μ:=by
  by_cases hτ:0<τ
  · have hs:∀ω,Integrable (fun x:HeatCircle=>‖value U V τ (ω,x)‖^2) haarAddCircle ∧
        (∫x:HeatCircle,‖value U V τ (ω,x)‖^2 ∂haarAddCircle)≤‖V ω-U ω‖^2:=by
      intro ω
      have hm:=PhysicalProfile.physicalHeatMean_memLp hτ (embed (V ω-U ω))
      have hb:=pow_le_pow_left₀ (normTwo_nonneg haarAddCircle _)
        (PhysicalProfile.physicalHeatMean_contraction hτ (embed (V ω-U ω))) 2
      rw [normTwo_sq,embed_norm] at hb
      simpa only [value,if_pos hτ,Real.norm_eq_abs,sq_abs] using And.intro hm.norm.integrable_sq hb
    have hh:=SectionEnergy.product_energy haarAddCircle μ (value U V τ) (value_measurable U V hU hV τ)
      (fun ω=>‖V ω-U ω‖^2) hdi (ae_of_all _ (fun ω=>(hs ω).1)) (ae_of_all _ (fun ω=>(hs ω).2))
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  · have hh:=NativeRepresentativeEnergy.product_energy μ U V hU hV hdi
    simpa only [value,if_neg hτ] using And.intro hh.1 hh.2.le

theorem damped_energy (μ:Measure Ω) [SFinite μ]
    (U V:Ω→RealL2) (hU:Measurable U) (hV:Measurable V)
    (hdi:Integrable (fun ω=>‖V ω-U ω‖^2) μ) (τ:ℝ)
    {a:ℝ} (ha:0≤a) (ha1:a≤1):
    Integrable (fun y=>(a*value U V τ y)^2) (μ.prod haarAddCircle) ∧
      (∫y,(a*value U V τ y)^2 ∂μ.prod haarAddCircle)≤∫ω,‖V ω-U ω‖^2 ∂μ:=by
  have hh:=product_energy μ U V hU hV hdi τ
  have hi:Integrable (fun y=>(a*value U V τ y)^2) (μ.prod haarAddCircle):=by
    simpa only [mul_pow] using hh.1.const_mul (a^2)
  refine ⟨hi,?_⟩
  simp only [mul_pow,integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hh.2 (sq_nonneg a)).trans
    (mul_le_of_le_one_left (integral_nonneg (fun _=>sq_nonneg _))
      (by nlinarith))

end SHE.NativeCurrentSourceEnergy
