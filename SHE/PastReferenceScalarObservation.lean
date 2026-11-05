module

public import SHE.PastFrozenPrefixRows
public import SHE.NativeObservationNaturality
public import SHE.PastReferencePropagation
public import SHE.NativeColumnHeatSemigroup
public import SHE.HilbertItoNaturality
public import SHE.PastReferenceStopped
public import SHE.PastReferenceIntegral
public import SHE.PastReferenceInput
public import SHE.PastItoAlgebra
public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PastReferenceScalarObservation
open Set MeasureTheory PredictableL2 ControlledProfile StoppedFourier PastItoInputs PastReferenceBracket StoppedItoInputs
open scoped NNReal ENNReal
local instance pastReferencePropagatedIntegral_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance pastReferencePropagatedIntegral_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance pastReferencePropagatedIntegral_instance3 : MeasurableSpace CircleL2 := borel _
local instance pastReferencePropagatedIntegral_instance4 : BorelSpace CircleL2 := ⟨rfl⟩
local instance pastReferencePropagatedIntegral_instance5 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance pastReferencePropagatedIntegral_instance6 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) {Λ κ : ℝ} (hΛ : 0≤Λ) (hκ : κ<P.lower)
variable (θ η : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (H v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
variable (data : Ω → Inputs) (hdata : Measurable[𝓕 v] data)
variable (hdi : Integrable (fun ω => ‖(data ω).2‖^2) μ)
local notation "Input" => input 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi
local notation "Cref" => energyConstant P κ θ η ((b:ℝ)-(v:ℝ))

attribute [local irreducible] PastReferenceBracket.input
open NativeHeatObservation NativeColumnHeatSemigroup
local instance pastReferencePropagatedIntegral_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

local instance pastReferencePropagatedIntegral_realSigma : MeasurableSpace DyadicApproximation.RealL2 := borel _
local instance pastReferencePropagatedIntegral_realBorel : BorelSpace DyadicApproximation.RealL2 := ⟨rfl⟩
local instance pastReferencePropagatedIntegral_rowSigma : MeasurableSpace FiniteHaar.RealHaarInput := borel _
local instance pastReferencePropagatedIntegral_rowBorel : BorelSpace FiniteHaar.RealHaarInput := ⟨rfl⟩


/-- Actual scalar observation row of the same frozen profile on its
original positive-gap prefix. -/
def row (T:ℝ) (ht:(b:ℝ)<T) (ξ:ℝ) (x:HeatCircle):
    Process (E:=FiniteHaar.RealHaarInput) 𝓕 μ H:=
  NativeObservationProcess.process 𝓕 μ H (sub_pos.mpr hκ)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκ)
    (FrozenReferenceFields.field P Λ κ ξ hκ v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ ξ hκ v data hdata) ht x

local notation "Row"=>row 𝓕 μ P (Λ:=Λ) hκ H v b data hdata

/-- The positive-age physical observation of the ACTUAL original
Hilbert frozen-difference input equals the original scalar post-v row
on the SAME Haar coordinates. This is an integrand theorem, with no
new stochastic-Fubini or reference-realization input. -/
theorem observed_input (T:ℝ) (ht:(b:ℝ)<T) (x:HeatCircle):
    ((columnFunctional (T-(b:ℝ)) x).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕))) Input=
      post 𝓕 μ H v (Row T ht θ x-Row T ht η x):=by
  apply PastItoAlgebra.eq_of_ambient_ae
  have hm:=ae_eq_of_ae_eq_trim ((columnFunctional (T-(b:ℝ)) x).coeFn_compLpL Input)
  have hi:=input_ae 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi
  have hp:=post_ae 𝓕 μ H v (Row T ht θ x-Row T ht η x)
  have hr:=ae_eq_of_ae_eq_trim (Lp.coeFn_sub (Row T ht θ x) (Row T ht η x))
  have hθ:=NativeObservationProcess.process_ae 𝓕 μ H (sub_pos.mpr hκ)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκ)
    (FrozenReferenceFields.field P Λ κ θ hκ v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκ v data hdata) ht x
  have hη:=NativeObservationProcess.process_ae 𝓕 μ H (sub_pos.mpr hκ)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκ)
    (FrozenReferenceFields.field P Λ κ η hκ v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ η hκ v data hdata) ht x
  filter_upwards [hm,hi,hp,hr,hθ,hη] with z hm hi hp hr hθ hη
  change Row T ht θ x z=_ at hθ
  change Row T ht η x z=_ at hη
  rw [hm,hi,hp]
  simp only [Pi.sub_apply,hr,hθ,hη]
  unfold PastReferenceBracket.raw NativeObservationProcess.integrand
  by_cases hv:v<z.1
  · rw [if_pos hv]
    by_cases hz:z.1≤b
    · rw [indicator_of_mem (show z∈Ioc v b×ˢ(univ:Set Ω) from ⟨⟨hv,hz⟩,mem_univ _⟩),map_sub]
    · rw [indicator_of_notMem (show z∉Ioc v b×ˢ(univ:Set Ω) from fun h=>hz h.1.2),map_zero]
      rw [NativeHeatObservation.kernel_zero (sub_pos.mpr hκ)
        (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hz))),
        NativeHeatObservation.kernel_zero (sub_pos.mpr hκ)
        (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hz))),map_zero,sub_self]
  · rw [if_neg hv,indicator_of_notMem
      (show z∉Ioc v b×ˢ(univ:Set Ω) from fun h=>hv h.1.1),map_zero]

/-- Ordinary scalar naturality on the SAME original residual channel
now gives the actual scalar frozen-reference observation identity. -/
theorem observe_integral
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=DyadicApproximation.RealL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hIJ:NativeObservationNaturality.StandardScalarNaturality I J)
    (T:ℝ) (ht:(b:ℝ)<T) (x:HeatCircle):
    (fun ω=>functional (T-(b:ℝ)) x (I.integral Input ω))=ᵐ[μ]
      J.integral (post 𝓕 μ H v (Row T ht θ x-Row T ht η x)):=by
  have he:=hIJ.commutes (functional (T-(b:ℝ)) x) Input
  change ((functional (T-(b:ℝ)) x).compLpL 2 μ) (I.integral Input)=
    J.integral (((columnFunctional (T-(b:ℝ)) x).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕))) Input) at he
  rw [observed_input 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi T ht x] at he
  have hc:=(functional (T-(b:ℝ)) x).coeFn_compLpL (I.integral Input)
  rw [he] at hc
  exact hc.symm

end SHE.PastReferenceScalarObservation
