module

public import SHE.NativeFrozenPrefixSmoothing
public import SHE.NativeFrozenSpatialObservation
public import SHE.NativeScalarProductAlgebra
public import SHE.NativeFixedHaarSemigroup
public import SHE.NativeFrozenHilbertField
public import SHE.NativeFixedHaarInput
public import SHE.NativeColumnHeatSemigroup
public import SHE.HilbertItoNaturality
public import SHE.NativeHeatFunctionalEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.NativeFrozenPrefixObservation
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation DyadicApproximation
open scoped NNReal ENNReal
local instance nativeFrozenPrefixObservation_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFrozenPrefixObservation_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFrozenPrefixObservation_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFrozenPrefixObservation_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFrozenPrefixObservation_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFrozenPrefixObservation_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeFrozenPrefixObservation_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeFrozenPrefixObservation_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance nativeFrozenPrefixObservation_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeFrozenPrefixObservation_realBorel : BorelSpace RealL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

variable (b c q v:ℝ≥0) (hbH:b≤H) (hb1:(b:ℝ)≤1) (hc0:0<c) (hcb:c<b) (hqc:q≤c)
variable (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ:NativeObservationNaturality.StandardScalarNaturality I J)
local notation "hcH"=>hcb.le.trans hbH
local notation "hc1"=>(show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb.le).trans hb1
local notation "Input"=>NativeFixedHaarSemigroup.stopped 𝓕 μ H hell hM f hf c hcH hc1 v q
local notation "Noise"=>NativeFrozenHilbertField.noise 𝓕 μ H c v hell hM f hf hcH hc1 I

include hIJ hc0 hqc in
/-- Every spatial root observes the exact SAME original scalar integral
through a bounded positive-prefix heat functional. -/
theorem noise_observation (B:ℝ≥0) (hBDG:StandardTerminalBDG16 I B) (x:StoppedFourier.HeatCircle):
    (fun ω=>functional ((b:ℝ)-(c:ℝ)) x (Noise q ω))=ᵐ[μ]
      J.integral (NativeFrozenSpatialObservation.row 𝓕 μ H b q v hell hM f hf hbH
        (hqc.trans hcb.le) x 0):=by
  have hε:0<(b:ℝ)-(c:ℝ):=sub_pos.mpr (by exact_mod_cast hcb)
  have hi:=hIJ.commutes (functional ((b:ℝ)-(c:ℝ)) x) Input
  change ((functional ((b:ℝ)-(c:ℝ)) x).compLpL 2 μ) (I.integral Input)=
    J.integral (((columnFunctional ((b:ℝ)-(c:ℝ)) x).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕))) Input) at hi
  rw [NativeFrozenSpatialObservation.observed_input 𝓕 μ H c q v hell hM f hf hcH hc1 hqc hε x] at hi
  have hr:NativeFrozenSpatialObservation.row 𝓕 μ H c q v hell hM f hf hcH hqc x ((b:ℝ)-(c:ℝ))=
      NativeFrozenSpatialObservation.row 𝓕 μ H b q v hell hM f hf hbH (hqc.trans hcb.le) x 0:=by
    simp only [NativeFrozenSpatialObservation.row,max_eq_left hε.le,max_self,add_zero,
      show (c:ℝ)+((b:ℝ)-(c:ℝ))=(b:ℝ) by ring]
  rw [hr] at hi
  have hv:=(functional ((b:ℝ)-(c:ℝ)) x).coeFn_compLpL (I.integral Input)
  rw [hi] at hv
  filter_upwards [hv,NativeFrozenHilbertField.noise_ae 𝓕 μ H c v hell hM f hf hcH hc1 I hc0 B hBDG q hqc] with ω hv hn
  rw [hn]
  exact hv.symm

include hIJ hc0 hqc in
/-- The canonical native representative equals that same bounded
positive-prefix scalar observation on a genuine root/sample event. -/
theorem noise_native (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B:ℝ≥0) (hBDG:StandardTerminalBDG16 I B):
    ∀ᵐ x:StoppedFourier.HeatCircle∂AddCircle.haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField
        (fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v hell hM f hf hbH hb1 I q ω) (ω,x)=
      functional ((b:ℝ)-(c:ℝ)) x (Noise q ω):=by
  have hm:Measurable (Noise q):=
    (((NativeFrozenHilbertField.noise_predictable 𝓕 μ H c v hell hM f hf hcH hc1 I hc0 hnull B hBDG).mono
      (predictable_le_product 𝓕)).measurable).comp (measurable_const.prodMk measurable_id)
  have ha:=NativeScalarProductAlgebra.heat_ae μ (Noise q) hm
    (sub_pos.mpr (show (c:ℝ)<(b:ℝ) by exact_mod_cast hcb))
  have hn:=NativeFrozenPrefixSmoothing.noise_factor 𝓕 μ H hell hM f hf I J hIJ b c q v
    hbH hb1 hc0 hcb.le hqc B hBDG
  filter_upwards [ha] with x hx
  filter_upwards [hx,hn] with ω hx hn
  rw [NativeScalarFieldAlgebra.congr
    (fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v hell hM f hf hbH hb1 I q ω)
    (fun ω=>heat ((b:ℝ)-(c:ℝ)) (Noise q ω)) ω hn x]
  exact hx

end SHE.NativeFrozenPrefixObservation
