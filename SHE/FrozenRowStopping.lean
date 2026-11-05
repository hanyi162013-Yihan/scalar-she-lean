module
public import SHE.ParametricStoppedHaarRows
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.FrozenRowStopping
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open scoped NNReal ENNReal
local instance frozenRowStopping_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance frozenRowStopping_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance frozenRowStopping_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H b q v:ℝ≥0)
variable {ell M:ℝ}(hell:0<ell)(hM:0≤M)
variable (f:ℝ≥0×Ω→EllipticField ell M)(hf:StronglyMeasurable[𝓕.predictable] f)
variable (hbH:b≤H)(hqb:q≤b)(x:HeatCircle)

theorem row_ae:
    NativeFrozenSpatialObservation.row 𝓕 μ H b q v hell hM f hf hbH hqb x 0=ᵐ[energyMeasure μ H]
      (fun p=>if v<p.1∧p.1<q then NativeObservationCovariance.row hell (f p) b p.1 x else 0):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hfu:StronglyMeasurable[((inferInstance:MeasurableSpace Unit).prod 𝓕.predictable)]
      (fun z:Unit×(ℝ≥0×Ω)=>f z.2):=hf.comp_measurable measurable_snd
  exact ParametricStoppedHaarRows.process_ae 𝓕 μ H hell hM (fun _:Unit=>v) (fun _=>b)
    (fun _=>q) (fun _=>x) (fun z=>f z.2) hfu (fun _=>hqb) (fun _=>hbH) ()

/-- Partial stopping of the genuine full-target post-past row is exactly
the original partial observation row, including q=b. -/
theorem stop_row:
    StoppedItoInputs.stop 𝓕 μ H (q:ℝ)
      (NativeFrozenSpatialObservation.row 𝓕 μ H b b v hell hM f hf hbH le_rfl x 0)=
    NativeFrozenSpatialObservation.row 𝓕 μ H b q v hell hM f hf hbH hqb x 0:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [StoppedItoInputs.stop_ae 𝓕 μ H (q:ℝ)
      (NativeFrozenSpatialObservation.row 𝓕 μ H b b v hell hM f hf hbH le_rfl x 0),
    row_ae 𝓕 μ H b b v hell hM f hf hbH le_rfl x,
    row_ae 𝓕 μ H b q v hell hM f hf hbH hqb x] with p hs hb hq
  rw [hs,hq]
  by_cases ht:p.1<q
  · rw [Set.indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) (q:ℝ) by exact_mod_cast ht),hb]
    by_cases hv:v<p.1
    · rw [if_pos ⟨hv,ht.trans_le hqb⟩,if_pos ⟨hv,ht⟩]
    · rw [if_neg (fun h=>hv h.1),if_neg (fun h=>hv h.1)]
  · rw [Set.indicator_of_notMem (show p∉StoppedItoInputs.before (Ω:=Ω) (q:ℝ) by exact_mod_cast ht),
      if_neg (fun h=>ht h.2)]
end SHE.FrozenRowStopping
