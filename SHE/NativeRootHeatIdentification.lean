module

public import SHE.NativeRootHeatLimit
public import SHE.PredictableScalarField

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeRootHeatLimit
open Set Filter MeasureTheory AddCircle StoppedFourier DyadicApproximation
open scoped ENNReal Topology
local instance nativeRootHeatIdentification_unit : Fact (0<(1:ℝ)) := ⟨by positivity⟩
local instance nativeRootHeatIdentification_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (a : ℝ→ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀z,|a z|≤M)

/-- The positive-gap Hilbert root is exactly the physical scalar root
evaluated at the native heat observation. -/
theorem root_ae_observation {t : ℝ} (ht : 0<t) (U : RealL2) :
    root a ha M hM t U=ᵐ[haarAddCircle (T:=2*Real.pi)]
      fun x=>(a (NativeHeatObservation.functional t x U):ℂ) := by
  let V:=NativeHeatObservation.heat t U
  have hpres:=(CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving
  have hc:=hpres.ae (CoefficientFields.coefficient_ae a ha M hM V)
  have hr:=hpres.ae (realEmbed_ae V)
  have hk:=StoppedFourier.heat_kernel_inner_ae ht (NativeHeatObservation.embed U)
  rw [←NativeHeatObservation.embed_heat ht.le U] at hk
  filter_upwards [CircleNormalization.push_ae (CoefficientFields.coefficient a ha M hM V),
    CircleNormalization.push_ae (realEmbed V),hc,hr,hk] with x hp he hc hr hk
  have hfun:NativeHeatObservation.functional t x U=V (CircleNormalization.scale (2*Real.pi) 1 x):=by
    rw [NativeHeatObservation.functional_apply,hk]
    change (CircleNormalization.push (realEmbed V) x).re=_
    rw [he,hr]
    rfl
  change CircleNormalization.push (CoefficientFields.coefficient a ha M hM V) x=_
  rw [hp,hc,hfun]

/-- The zero-gap Hilbert root is the ORIGINAL chosen native scalar
representative, for arbitrary dependent states and parameter spaces. -/
theorem root_zero_ae {X : Type*} (U : X→RealL2) (p : X) :
    root a ha M hM 0 (U p)=ᵐ[haarAddCircle (T:=2*Real.pi)]
      fun x=>(a (PredictableScalarField.nativeField U (p,x)):ℂ) := by
  rw [root_zero]
  have he:=PredictableScalarField.nativeField_coefficient_ae a ha M hM U p
  have hr:=CircleNormalization.push_ae_property (CoefficientFields.coefficient a ha M hM (U p))
    (fun z:ℂ=>z.im=0) (CoefficientFields.coefficient_real a ha M hM (U p))
  filter_upwards [he,hr] with x he hr
  exact Complex.ext he (by simpa only [Complex.ofReal_im] using hr)

end SHE.NativeRootHeatLimit
