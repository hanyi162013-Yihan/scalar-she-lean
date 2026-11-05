module

public import SHE.NativeFixedHaarSemigroup
public import SHE.NativeFrozenHilbertField
public import SHE.NativeFixedHaarInput
public import SHE.NativeColumnHeatSemigroup
public import SHE.HilbertItoNaturality
public import SHE.NativeHeatFunctionalEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.NativeFrozenPrefixSmoothing
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation DyadicApproximation
open scoped NNReal ENNReal
local instance nativeFrozenPrefixSmoothing_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFrozenPrefixSmoothing_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFrozenPrefixSmoothing_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFrozenPrefixSmoothing_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFrozenPrefixSmoothing_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFrozenPrefixSmoothing_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeFrozenPrefixSmoothing_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeFrozenPrefixSmoothing_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

open NativeFixedHaarSemigroup

/-- Positive target smoothing commutes with an independently stopped
frozen input. The old time and current stop are unchanged. -/
theorem heat_stopped (b c q v:ℝ≥0) (hbH:b≤H) (hb1:(b:ℝ)≤1)
    (hcb:c≤b) (hqc:q≤c):
    ((HilbertColumns.mapCLM (heat ((b:ℝ)-(c:ℝ)))).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))
      (stopped 𝓕 μ H hell hM f hf c (hcb.trans hbH)
        ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb).trans hb1) v q)=
    stopped 𝓕 μ H hell hM f hf b hbH hb1 v q:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM (heat ((b:ℝ)-(c:ℝ)))).coeFn_compLpL
      (stopped 𝓕 μ H hell hM f hf c (hcb.trans hbH)
        ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb).trans hb1) v q)),
    stopped_ae 𝓕 μ H hell hM f hf c (hcb.trans hbH)
      ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb).trans hb1) v q,
    stopped_ae 𝓕 μ H hell hM f hf b hbH hb1 v q] with p hm hc hb
  rw [hm,hc,hb]
  split_ifs with h
  · rw [NativeColumnHeatSemigroup.map_kernel hell (sub_nonneg.mpr (by exact_mod_cast hcb))
      (sub_pos.mpr (show (p.1:ℝ)<(c:ℝ) from
        (show (p.1:ℝ)<(q:ℝ) by exact_mod_cast h.2).trans_le (by exact_mod_cast hqc)))]
    congr 1
    ring
  · exact map_zero _

variable (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ:NativeObservationNaturality.StandardScalarNaturality I J)

include hIJ in
theorem heat_integral (b c q v:ℝ≥0) (hbH:b≤H) (hb1:(b:ℝ)≤1)
    (hcb:c≤b) (hqc:q≤c):
    (fun ω=>heat ((b:ℝ)-(c:ℝ)) (I.integral (stopped 𝓕 μ H hell hM f hf c
      (hcb.trans hbH) ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb).trans hb1) v q) ω))=ᵐ[μ]
    I.integral (stopped 𝓕 μ H hell hM f hf b hbH hb1 v q):=by
  have he:=HilbertItoNaturality.commutes 𝓕 μ H I J hIJ (heat ((b:ℝ)-(c:ℝ)))
    (stopped 𝓕 μ H hell hM f hf c (hcb.trans hbH)
      ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb).trans hb1) v q)
  rw [heat_stopped 𝓕 μ H hell hM f hf b c q v hbH hb1 hcb hqc] at he
  exact he

include hIJ in
/-- The actual continuous frozen Hilbert noise on any positive prefix
is a fixed positive heat smoothing of another actual continuous noise. -/
theorem noise_factor (b c q v:ℝ≥0) (hbH:b≤H) (hb1:(b:ℝ)≤1)
    (hc0:0<c) (hcb:c≤b) (hqc:q≤c) (B:ℝ≥0) (hBDG:StandardTerminalBDG16 I B):
    (fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v hell hM f hf hbH hb1 I q ω)=ᵐ[μ]
    (fun ω=>heat ((b:ℝ)-(c:ℝ)) (NativeFrozenHilbertField.noise 𝓕 μ H c v hell hM f hf
      (hcb.trans hbH) ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb).trans hb1) I q ω)):=by
  filter_upwards [NativeFrozenHilbertField.noise_ae 𝓕 μ H b v hell hM f hf hbH hb1 I
      (hc0.trans_le hcb) B hBDG q (hqc.trans hcb),
    NativeFrozenHilbertField.noise_ae 𝓕 μ H c v hell hM f hf (hcb.trans hbH)
      ((show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb).trans hb1) I hc0 B hBDG q hqc,
    heat_integral 𝓕 μ H hell hM f hf I J hIJ b c q v hbH hb1 hcb hqc] with ω hb hc he
  rw [hb,hc]
  exact he.symm

end SHE.NativeFrozenPrefixSmoothing
