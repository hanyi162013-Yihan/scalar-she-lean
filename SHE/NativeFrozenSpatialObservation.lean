module

public import SHE.NativeFixedHaarSemigroup
public import SHE.NativeFrozenHilbertField
public import SHE.FullHorizonTargetContinuity
public import SHE.HeatObservationEndpointLimit
public import SHE.PastItoContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeFrozenSpatialObservation
open Set MeasureTheory AddCircle PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation DyadicApproximation
open Filter Topology
open scoped NNReal ENNReal
local instance nativeFrozenSpatialObservation_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFrozenSpatialObservation_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFrozenSpatialObservation_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFrozenSpatialObservation_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFrozenSpatialObservation_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeFrozenSpatialObservation_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeFrozenSpatialObservation_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFrozenSpatialObservation_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeFrozenSpatialObservation_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance nativeFrozenSpatialObservation_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance nativeFrozenSpatialObservation_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeFrozenSpatialObservation_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b q v : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (hbH : b≤H) (hb1 : (b:ℝ)≤1) (hqb : q≤b)

local notation "Input"=>NativeFixedHaarSemigroup.stopped 𝓕 μ H hell hM f hf b hbH hb1 v q

def row (x : HeatCircle) (ε : ℝ) : Process (E:=RealHaarInput) 𝓕 μ H:=
  PastItoInputs.post 𝓕 μ H v
    (FullHorizonEndpoint.process 𝓕 μ H q hell hM f hf
      (show (q:ℝ)≤(b:ℝ)+max ε 0 by linarith [NNReal.coe_le_coe.mpr hqb,le_max_right ε 0])
      x (hqb.trans hbH))

theorem observed_input {ε : ℝ} (hε : 0<ε) (x : HeatCircle) :
    ((columnFunctional ε x).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) Input=
      row 𝓕 μ H b q v hell hM f hf hbH hqb x ε := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim ((columnFunctional ε x).coeFn_compLpL Input),
    NativeFixedHaarSemigroup.stopped_ae 𝓕 μ H hell hM f hf b hbH hb1 v q,
    PastItoInputs.post_ae 𝓕 μ H v
      (FullHorizonEndpoint.process 𝓕 μ H q hell hM f hf
        (show (q:ℝ)≤(b:ℝ)+max ε 0 by linarith [NNReal.coe_le_coe.mpr hqb,le_max_right ε 0]) x (hqb.trans hbH)),
    FullHorizonEndpoint.process_ae 𝓕 μ H q hell hM f hf
      (show (q:ℝ)≤(b:ℝ)+max ε 0 by linarith [NNReal.coe_le_coe.mpr hqb,le_max_right ε 0]) x (hqb.trans hbH)] with p hm hi hp hr
  change row 𝓕 μ H b q v hell hM f hf hbH hqb x ε p=_ at hp
  rw [hm,hi,hp]
  by_cases hv : v<p.1
  · rw [if_pos hv]
    by_cases hq : p.1<q
    · rw [if_pos ⟨hv,hq⟩,hr,FullHorizonEndpoint.raw,
        indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from by exact_mod_cast hq),
        NativeObservationEndpoint.fullIntegrand,if_pos (show (p.1:ℝ)<(b:ℝ)+max ε 0 by
          linarith [NNReal.coe_lt_coe.mpr hq,NNReal.coe_le_coe.mpr hqb,le_max_right ε 0])]
      rw [NativeHeatObservation.observed_kernel_eq hell hε
        (sub_pos.mpr (lt_of_lt_of_le (by exact_mod_cast hq) (by exact_mod_cast hqb)))]
      congr 2
      rw [max_eq_left hε.le]
      ring
    · rw [if_neg (fun h=>hq h.2),map_zero,hr,FullHorizonEndpoint.raw,
        indicator_of_notMem (show p∉StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from by exact_mod_cast hq)]
  · rw [if_neg hv,if_neg (fun h=>hv h.1),map_zero]

variable (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ : NativeObservationNaturality.StandardScalarNaturality I J)

include hIJ in
/-- The genuine jointly measurable native spatial representative is
identified with the SAME scalar-J frozen observation for almost every
root, by a proved heat-endpoint limit. No pointwise L2 evaluation or
joint measurability of arbitrarily selected scalar versions is assumed. -/
theorem physical_observation :
    ∀ᵐ x : HeatCircle∂haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField (I.integral Input) (ω,x)=
        J.integral (row 𝓕 μ H b q v hell hM f hf hbH hqb x 0) ω := by
  suffices hres : ∀ᵐ x : HeatCircle∂haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField (I.integral Input) (ω,x)=
        0+J.integral (row 𝓕 μ H b q v hell hM f hf hbH hqb x 0) ω by
    simpa only [zero_add] using hres
  apply HeatObservationEndpointLimit.physical_endpoint 𝓕 μ H J (I.integral Input)
    (Lp.stronglyMeasurable _).measurable (row 𝓕 μ H b q v hell hM f hf hbH hqb) (fun _ _=>0)
  · intro x
    exact continuous_const.continuousAt
  · intro ε hε hε0 x
    have htarget : Tendsto (fun n=>(b:ℝ)+max (ε n) 0) atTop (𝓝 (b:ℝ)) := by
      have hm : Tendsto (fun n=>max (ε n) (0:ℝ)) atTop (𝓝 (max (0:ℝ) 0)):=hε0.max tendsto_const_nhds
      simpa only [max_self,add_zero] using (show Tendsto (fun n=>(b:ℝ)+max (ε n) 0) atTop (𝓝 ((b:ℝ)+max (0:ℝ) 0)) from tendsto_const_nhds.add hm)
    have hh:=FullHorizonTargetContinuity.tendsto 𝓕 μ H q hell hM f hf (hqb.trans hbH)
      (show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb) (fun n=>(b:ℝ)+max (ε n) 0)
      (fun n=>by linarith [NNReal.coe_le_coe.mpr hqb,le_max_right (ε n) 0]) htarget x
    have hp:=(PastItoContinuity.lipschitz (C:=RealHaarInput) 𝓕 μ H v).continuous.tendsto _ |>.comp hh
    simpa [row,Function.comp_def] using hp
  · intro ε hε x
    have he:=hIJ.commutes (functional ε x) Input
    change ((functional ε x).compLpL 2 μ) (I.integral Input)=
      J.integral (((columnFunctional ε x).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) Input) at he
    rw [observed_input 𝓕 μ H b q v hell hM f hf hbH hb1 hqb hε x] at he
    have hc:=(functional ε x).coeFn_compLpL (I.integral Input)
    rw [he] at hc
    simpa only [zero_add] using hc.symm

end SHE.NativeFrozenSpatialObservation
