module

public import SHEStochastic.NativeRemainderObservation
public import SHE.PredictableScalarField

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeScalarSectionRecognition
open MeasureTheory SHE SHE.DyadicApproximation SHE.StoppedFourier HeatParameterCover HeatParameterPullback
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩

/-- The existing joint scalar representative agrees with the actual
physical L2 state in each spatial section. -/
theorem native_push_ae {P : Type*} (V : P → RealL2) (p : P) :
    (fun x => PredictableScalarField.nativeField V (p,x)) =ᵐ[AddCircle.haarAddCircle (T := 2*Real.pi)]
      NativePhysicalState.push (V p) :=
  (PredictableScalarField.nativeField_ae_unit V p).trans (NativePhysicalState.push_ae (V p)).symm

theorem heat_push_ae {r : ℝ} (hr : 0 < r) (u : RealL2) :
    NativePhysicalState.push (NativeHeatObservation.heat r u) =ᵐ[AddCircle.haarAddCircle (T := 2*Real.pi)]
      fun x => PhysicalProfile.physicalHeatMean (NativeHeatObservation.embed u) (r,x) := by
  rw [NativePhysicalState.push_heat hr.le,PhysicalHeatState.state_eq_value hr]
  exact PhysicalHeatSmoothing.value_ae 2 r hr _

theorem remainder_push_ae (Y : C(Parameter,ℝ)) (t : ShortTime) :
    NativePhysicalState.push (NativeRemainderObservation.remainder Y t) =ᵐ[AddCircle.haarAddCircle (T := 2*Real.pi)]
      fun x => Y (point t x) := by
  change NativePhysicalState.push (NativePhysicalState.pull (PhysicalHeatParameterSection.value 2 Y t)) =ᵐ[_] _
  rw [NativePhysicalState.push_pull]
  exact PhysicalHeatParameterSection.value_ae 2 Y t

/-- An actual spatial endpoint identity identifies the native L2 state.
Ordinary Fubini changes the order of the spatial and sample null sets;
no point-evaluation convention for an L2 class is assumed. -/
theorem state_eq_random {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → RealL2) (hV : Measurable V) (Z : Ω → RealL2) (hZ : Measurable Z) {r : ℝ} (hr : 0 < r)
    (Y : Ω → C(Parameter,ℝ)) (hY : Measurable Y) (t : ShortTime)
    (hpoint : ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      PredictableScalarField.nativeField V (ω,x) =
        PhysicalProfile.physicalHeatMean (NativeHeatObservation.embed (Z ω)) (r,x)+Y ω (point t x)) :
    V =ᵐ[μ] fun ω => NativeHeatObservation.heat r (Z ω)+NativeRemainderObservation.remainder (Y ω) t := by
  have hleft : Measurable (fun z : HeatCircle × Ω => PredictableScalarField.nativeField V (z.2,z.1)) :=
    (PredictableScalarField.nativeField_measurable hV).comp (measurable_snd.prodMk measurable_fst)
  have hmean : Measurable (fun z : HeatCircle × Ω =>
      PhysicalProfile.physicalHeatMean (NativeHeatObservation.embed (Z z.2)) (r,z.1)) :=
    PhysicalProfile.physicalHeatMean_joint_measurable.comp
      ((NativeHeatObservation.embed.continuous.measurable.comp (hZ.comp measurable_snd)).prodMk
        (measurable_const.prodMk measurable_fst))

  have hp : Measurable (point t) := measurable_point.comp (measurable_const.prodMk measurable_id)
  have hfield : Measurable (fun z : HeatCircle × Ω => Y z.2 (point t z.1)) :=
    continuous_eval.measurable.comp ((hY.comp measurable_snd).prodMk (hp.comp measurable_fst))
  have hjoint := (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hleft (hmean.add hfield))).mpr hpoint
  have hswap := (Measure.measurePreserving_swap (μ := μ)
    (ν := AddCircle.haarAddCircle (T := 2*Real.pi))).quasiMeasurePreserving.ae hjoint
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  apply NativePhysicalState.push.injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [hω,native_push_ae V ω,heat_push_ae hr (Z ω),remainder_push_ae (Y ω) t,
    Lp.coeFn_add (NativePhysicalState.push (NativeHeatObservation.heat r (Z ω)))
      (NativePhysicalState.push (NativeRemainderObservation.remainder (Y ω) t))] with x he hn hh hy ha
  rw [ha,Pi.add_apply,hh,hy,← hn]
  exact he


theorem state_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → RealL2) (hV : Measurable V) (u : RealL2) {r : ℝ} (hr : 0 < r)
    (Y : Ω → C(Parameter,ℝ)) (hY : Measurable Y) (t : ShortTime)
    (hpoint : ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      PredictableScalarField.nativeField V (ω,x) =
        PhysicalProfile.physicalHeatMean (NativeHeatObservation.embed u) (r,x)+Y ω (point t x)) :
    V =ᵐ[μ] fun ω => NativeHeatObservation.heat r u+NativeRemainderObservation.remainder (Y ω) t := by
  exact state_eq_random μ V hV (fun _ => u) measurable_const hr Y hY t hpoint

end SHEStochastic.NativeScalarSectionRecognition
