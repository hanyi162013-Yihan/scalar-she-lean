module
public import SHE.BoundedPastItoMultiplier
public import SHE.PredictableSteps
public import SHE.RotatedCylindricalCoordinates
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.BoundedHilbertItoCell
open MeasureTheory FiniteHaar DyadicApproximation PredictableL2 NativeObservationNaturality
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H v r:ℝ≥0)
variable (i:HaarNode)(Z:Ω→RealL2)(hZ:StronglyMeasurable[𝓕 v] Z)(K:ℝ)(hb:∀ω,‖Z ω‖≤K)

include hZ in
theorem column_measurable:StronglyMeasurable[𝓕 v] (fun ω=>lp.single (E:=fun _:HaarNode=>RealL2) 2 i (Z ω)):=
  (lp.isometry_single (p:=2) i).continuous.comp_stronglyMeasurable hZ

include hZ hb in
theorem column_memLp:MemLp (fun ω=>lp.single (E:=fun _:HaarNode=>RealL2) 2 i (Z ω)) 2 μ:=by
  apply MemLp.of_bound ((column_measurable 𝓕 v i Z hZ).mono (𝓕.le v)).aestronglyMeasurable K
  exact ae_of_all _ (fun ω=>by rw [lp.norm_single (by norm_num:0<(2:ENNReal))];exact hb ω)

/-- The actual bounded past-known physical column in the original
Hilbert stochastic-integral input space. -/
def input:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  PredictableSteps.process 𝓕 μ H v r (fun ω=>lp.single (E:=fun _:HaarNode=>RealL2) 2 i (Z ω))
    (column_measurable 𝓕 v i Z hZ) (column_memLp 𝓕 μ v i Z hZ K hb)

theorem input_ae:
    input 𝓕 μ H v r i Z hZ K hb=ᵐ[energyMeasure μ H]
      PredictableSteps.step v r (fun ω=>lp.single (E:=fun _:HaarNode=>RealL2) 2 i (Z ω)):=
  PredictableSteps.process_ae 𝓕 μ H v r _ _ _

def observed_input (L:RealL2→L[ℝ] ℝ):Process (E:=RealHaarInput) 𝓕 μ H:=
  ((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕)))
    (input 𝓕 μ H v r i Z hZ K hb)

theorem observed_input_ae (L:RealL2→L[ℝ] ℝ):
    observed_input 𝓕 μ H v r i Z hZ K hb L=ᵐ[energyMeasure μ H]
      (fun p=>if p.1∈Set.Ioc v r then lp.single (E:=fun _:HaarNode=>ℝ) 2 i (L (Z p.2)) else 0):=by
  filter_upwards [ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLpL
      (input 𝓕 μ H v r i Z hZ K hb)),input_ae 𝓕 μ H v r i Z hZ K hb] with p hm hu
  change observed_input 𝓕 μ H v r i Z hZ K hb L p=_
  unfold observed_input
  rw [hm,hu]
  unfold PredictableSteps.step
  split_ifs
  · exact HilbertColumns.mapCLM_single L i (Z p.2)
  · exact map_zero _

def driver (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)(s:ℝ≥0)(ω:Ω):ℝ:=
  J.integral (StoppedItoInputs.stop 𝓕 μ H s
    (RotatedCylindricalCoordinates.constant 𝓕 μ H (lp.single 2 i (1:ℝ)))) ω

/-- Exact weak Hilbert time-cell integration, derived from scalar
past pullout and ordinary bounded-linear Ito naturality. -/
theorem observed_integral (hK:0≤K)(hvr:v≤r)
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hIJ:StandardScalarNaturality I J)(hlocal:StandardTerminalPastLocality J)
    (L:RealL2→L[ℝ] ℝ):
    (fun ω=>L (I.integral (input 𝓕 μ H v r i Z hZ K hb) ω))=ᵐ[μ]
      (fun ω=>L (Z ω)*(driver 𝓕 μ H i J r ω-driver 𝓕 μ H i J v ω)):=by
  let b:Process (E:=RealHaarInput) 𝓕 μ H:=
    RotatedCylindricalCoordinates.constant 𝓕 μ H (lp.single 2 i (1:ℝ))
  have hα:StronglyMeasurable[𝓕 v] (fun ω=>L (Z ω)):=L.continuous.comp_stronglyMeasurable hZ
  have hαb:∀ω,|L (Z ω)|≤‖L‖*K:=fun ω=>by
    rw [←Real.norm_eq_abs]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb ω) (norm_nonneg _))
  obtain ⟨R,hR,hJR⟩:=BoundedPastItoMultiplier.increment 𝓕 μ H v J hlocal r hvr b
    (fun ω=>L (Z ω)) hα (‖L‖*K) (mul_nonneg (norm_nonneg _) hK) hαb
  have he:observed_input 𝓕 μ H v r i Z hZ K hb L=R:=by
    apply PastItoAlgebra.eq_of_ambient_ae 𝓕 μ H
    have hne:∀ᵐp∂energyMeasure μ H,p.1≠r:=
      Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne r)
    filter_upwards [observed_input_ae 𝓕 μ H v r i Z hZ K hb L,hR,
      RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (lp.single (E:=fun _:HaarNode=>ℝ) 2 i (1:ℝ)),hne] with p ho hr hc hn
    rw [ho,hr,hc]
    have hlt:p.1≤r ↔ p.1<r:=⟨fun h=>lt_of_le_of_ne h hn,fun h=>h.le⟩
    simp only [Set.mem_Ioc,hlt]
    split_ifs
    · simpa only [smul_eq_mul,mul_one] using
        (lp.single_smul (E:=fun _:HaarNode=>ℝ) 2 i (L (Z p.2)) (1:ℝ))
    · rfl
  have hm:=L.coeFn_compLpL (I.integral (input 𝓕 μ H v r i Z hZ K hb))
  rw [hIJ.commutes L _,←observed_input,he] at hm
  filter_upwards [hm,hJR] with ω hm hj
  exact hm.symm.trans hj

/-- The actual Hilbert cell integral equals its physical coefficient
times the original Brownian-coordinate increment. Countable Hilbert
duality makes the scalar identities one genuine vector AE identity. -/
theorem integral (hK:0≤K)(hvr:v≤r)
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hIJ:StandardScalarNaturality I J)(hlocal:StandardTerminalPastLocality J):
    I.integral (input 𝓕 μ H v r i Z hZ K hb)=ᵐ[μ]
      (fun ω=>(driver 𝓕 μ H i J r ω-driver 𝓕 μ H i J v ω) • Z ω):=by
  have hf:(fun ω=>I.integral (input 𝓕 μ H v r i Z hZ K hb) ω-
      (driver 𝓕 μ H i J r ω-driver 𝓕 μ H i J v ω) • Z ω)=ᵐ[μ] 0:=by
    apply ae_eq_zero_of_forall_inner (𝕜:=ℝ)
    intro c
    have hh:=observed_integral 𝓕 μ H v r i Z hZ K hb hK hvr I J hIJ hlocal (innerSL ℝ c)
    filter_upwards [hh] with ω hω
    change inner ℝ c (I.integral (input 𝓕 μ H v r i Z hZ K hb) ω-
      (driver 𝓕 μ H i J r ω-driver 𝓕 μ H i J v ω) • Z ω)=0
    simp only [inner_sub_right,inner_smul_right]
    change (innerSL ℝ c) (I.integral (input 𝓕 μ H v r i Z hZ K hb) ω)-
      (driver 𝓕 μ H i J r ω-driver 𝓕 μ H i J v ω)*(innerSL ℝ c) (Z ω)=0
    rw [hω]
    ring
  filter_upwards [hf] with ω hω
  exact sub_eq_zero.mp hω
end SHE.BoundedHilbertItoCell
