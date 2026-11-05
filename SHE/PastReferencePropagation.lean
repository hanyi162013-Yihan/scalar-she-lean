module

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
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastReferencePropagation
open Set MeasureTheory PredictableL2 ControlledProfile StoppedFourier PastItoInputs PastReferenceBracket StoppedItoInputs
open scoped NNReal ENNReal
local instance pastReferencePropagation_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance pastReferencePropagation_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance pastReferencePropagation_instance3 : MeasurableSpace CircleL2 := borel _
local instance pastReferencePropagation_instance4 : BorelSpace CircleL2 := ⟨rfl⟩
local instance pastReferencePropagation_instance5 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance pastReferencePropagation_instance6 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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
local instance pastReferencePropagation_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

/-- Propagating the actual past-to-current compatible frozen integral
input to the fixed final target is exactly stopping the full-target
input. The frozen coefficient profile is unchanged. -/
theorem input_propagation (s : ℝ≥0) (hvs : v<s) (hsb : s≤b) :
    let hsH:=hsb.trans hbH
    let hst : (s:ℝ)-(v:ℝ)≤P.horizon:=(sub_le_sub_right (by exact_mod_cast hsb) _).trans hsmallTime
    ((HilbertColumns.mapCLM (NativeHeatObservation.heat ((b:ℝ)-(s:ℝ)))).compLpL 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))
      (PastReferenceBracket.input 𝓕 μ P hΛ hκ θ η hsmall H v s hvs hsH hst data hdata hdi)=
      StoppedItoInputs.stop 𝓕 μ H (s:ℝ) Input := by
  intro hsH hst
  let Sinput:=PastReferenceBracket.input 𝓕 μ P hΛ hκ θ η hsmall H v s hvs hsH hst data hdata hdi
  let A : RealHaarIntegrand.Columns →L[ℝ] RealHaarIntegrand.Columns:=HilbertColumns.mapCLM (NativeHeatObservation.heat ((b:ℝ)-(s:ℝ)))
  have hA:=ae_eq_of_ae_eq_trim (A.coeFn_compLpL Sinput)
  have hne : ∀ᵐ p ∂energyMeasure μ H,p.1≠s:=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne s)
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [hA,PastReferenceBracket.input_ae 𝓕 μ P hΛ hκ θ η hsmall H v s hvs hsH hst data hdata hdi,
    PastReferenceBracket.input_ae 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi,
    stop_ae 𝓕 μ H (s:ℝ) Input,hne] with p hA hs hi hstop hn
  rw [hA]
  change A (Sinput p)=(stop 𝓕 μ H (s:ℝ) Input) p
  rw [hs,hstop]
  by_cases hr : p.1∈Ioc v s
  · have hrs : p.1<s:=lt_of_le_of_ne hr.2 hn
    have hrB : p.1∈Ioc v b:=⟨hr.1,hr.2.trans hsb⟩
    have hsp : p∈Ioc v s×ˢ (univ:Set Ω):=⟨hr,mem_univ _⟩
    have hbp : p∈Ioc v b×ˢ (univ:Set Ω):=⟨hrB,mem_univ _⟩
    have hbefore : p∈before (Ω:=Ω) (s:ℝ):=by change (p.1:ℝ)<(s:ℝ);exact_mod_cast hrs
    rw [indicator_of_mem hbefore,hi]
    simp only [PastReferenceBracket.raw,indicator_of_mem hsp,indicator_of_mem hbp]
    dsimp only [A]
    rw [map_sub,map_kernel (sub_pos.mpr hκ) (sub_nonneg.mpr (by exact_mod_cast hsb))
      (sub_pos.mpr (by exact_mod_cast hrs)),
      map_kernel (sub_pos.mpr hκ) (sub_nonneg.mpr (by exact_mod_cast hsb))
      (sub_pos.mpr (by exact_mod_cast hrs))]
    simp only [show ((b:ℝ)-(s:ℝ))+((s:ℝ)-(p.1:ℝ))=(b:ℝ)-(p.1:ℝ) by ring]
  · have hsp : p∉Ioc v s×ˢ (univ:Set Ω):=fun hp=>hr hp.1
    simp only [PastReferenceBracket.raw,indicator_of_notMem hsp,map_zero]
    by_cases hbefore : p∈before (Ω:=Ω) (s:ℝ)
    · rw [indicator_of_mem hbefore,hi]
      have hrv : ¬v<p.1:=by
        intro hv
        apply hr
        exact ⟨hv,(by exact_mod_cast (le_of_lt hbefore))⟩
      have hbp : p∉Ioc v b×ˢ (univ:Set Ω):=fun hp=>hrv hp.1.1
      rw [PastReferenceBracket.raw,indicator_of_notMem hbp]
    · rw [indicator_of_notMem hbefore]

end SHE.PastReferencePropagation
