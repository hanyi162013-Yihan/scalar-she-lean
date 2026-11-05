module

public import SHE.NativeFixedHaarInput
public import SHE.NativeColumnHeatSemigroup
public import SHE.HilbertItoNaturality
public import SHE.NativeHeatFunctionalEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.NativeFixedHaarSemigroup
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation DyadicApproximation
open scoped NNReal ENNReal
local instance nativeFixedHaarSemigroup_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFixedHaarSemigroup_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFixedHaarSemigroup_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFixedHaarSemigroup_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFixedHaarSemigroup_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFixedHaarSemigroup_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeFixedHaarSemigroup_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeFixedHaarSemigroup_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

def stopped (T : ℝ≥0) (hTH : T≤H) (hT1 : (T:ℝ)≤1) (v q : ℝ≥0) :
    Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  StoppedItoInputs.stop 𝓕 μ H (q:ℝ)
    (PastItoInputs.post 𝓕 μ H v (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf T hTH hT1))

theorem stopped_ae (T : ℝ≥0) (hTH : T≤H) (hT1 : (T:ℝ)≤1) (v q : ℝ≥0) :
    stopped 𝓕 μ H hell hM f hf T hTH hT1 v q=ᵐ[energyMeasure μ H]
      (fun p=>if v<p.1 ∧ p.1<q then NativeHeatObservation.kernel ell M hell ((T:ℝ)-(p.1:ℝ),f p) else 0) := by
  filter_upwards [StoppedItoInputs.stop_ae 𝓕 μ H (q:ℝ)
      (PastItoInputs.post 𝓕 μ H v (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf T hTH hT1)),
    PastItoInputs.post_ae 𝓕 μ H v (NativeFixedHaarInput.input 𝓕 μ H hell hM f hf T hTH hT1),
    NativeFixedHaarInput.input_ae 𝓕 μ H hell hM f hf T hTH hT1] with p hs hp hi
  change StoppedItoInputs.stop 𝓕 μ H (q:ℝ) _ p=_
  rw [hs]
  by_cases hq : p.1<q
  · rw [indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from by exact_mod_cast hq),hp]
    by_cases hv : v<p.1 <;> simp only [hv,hq,and_true,and_self,ite_true,ite_false,hi,NativeFixedHaarInput.raw]
  · rw [indicator_of_notMem (show p∉StoppedItoInputs.before (Ω:=Ω) (q:ℝ) from by exact_mod_cast hq),
      if_neg (fun h=>hq h.2)]

/-- Literal semigroup propagation of the same stopped original input,
with no fresh noise, changed stopping time or clock normalization. -/
theorem heat_input (b q v : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1) (hqb : q≤b) :
    ((HilbertColumns.mapCLM (heat ((b:ℝ)-(q:ℝ)))).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))
      (stopped 𝓕 μ H hell hM f hf q (hqb.trans hbH) ((show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb).trans hb1) v q)=
    stopped 𝓕 μ H hell hM f hf b hbH hb1 v q := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM (heat ((b:ℝ)-(q:ℝ)))).coeFn_compLpL
      (stopped 𝓕 μ H hell hM f hf q (hqb.trans hbH) ((show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb).trans hb1) v q)),
    stopped_ae 𝓕 μ H hell hM f hf q (hqb.trans hbH) ((show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb).trans hb1) v q,
    stopped_ae 𝓕 μ H hell hM f hf b hbH hb1 v q] with p hm hq hb
  rw [hm,hq,hb]
  split_ifs with h
  · rw [NativeColumnHeatSemigroup.map_kernel hell (sub_nonneg.mpr (by exact_mod_cast hqb))
      (sub_pos.mpr (by exact_mod_cast h.2))]
    congr 1
    ring
  · exact map_zero _

variable (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ : NativeObservationNaturality.StandardScalarNaturality I J)

include hIJ in
/-- Actual full-target partial Hilbert martingale equals propagation
of the current-target frozen convolution on the SAME original channel.
This is the bridge to positive-age physical observations. -/
theorem heat_integral (b q v : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1) (hqb : q≤b) :
    (fun ω=>heat ((b:ℝ)-(q:ℝ))
      (I.integral (stopped 𝓕 μ H hell hM f hf q (hqb.trans hbH)
        ((show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb).trans hb1) v q) ω))=ᵐ[μ]
      I.integral (stopped 𝓕 μ H hell hM f hf b hbH hb1 v q) := by
  have he:=HilbertItoNaturality.commutes 𝓕 μ H I J hIJ (heat ((b:ℝ)-(q:ℝ)))
    (stopped 𝓕 μ H hell hM f hf q (hqb.trans hbH) ((show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb).trans hb1) v q)
  rw [heat_input 𝓕 μ H hell hM f hf b q v hbH hb1 hqb] at he
  exact he

end SHE.NativeFixedHaarSemigroup
