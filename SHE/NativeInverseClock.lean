module
public import SHE.TimeDilationRoundTrip
public import Mathlib.Analysis.Real.Pi.Bounds
public import SHE.TimeDilationPathPull
public import SHE.NativeClock
public import SHE.NativeSmoothFirstConstruction
import all SHE.NativeSmoothFirstConstruction
import all SHE.NativeMildFromUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.NativeInverseClock
open MeasureTheory PredictableL2 PredictableTimeDilation LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable{Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(Q:Measure Ω)[IsProbabilityMeasure Q](H:ℝ≥0)
local notation "rate"=>NativeClock.rate
local notation "rp"=>NativeClock.rate_pos

def base:Filtration ℝ≥0 ‹MeasurableSpace Ω›:=filtration 𝓕 (clock rate rp).symm

theorem filtration_eq:filtration (base 𝓕) (clock rate rp)=𝓕:=
  filtration_inverse_clock rate rp 𝓕

theorem span_eq:rate*NativeClock.time H=H:=by
  change clock rate rp ((clock rate rp).symm H)=H
  exact (clock rate rp).apply_symm_apply H

theorem time_le_one(hH:(H:ℝ)≤1):(NativeClock.time H:ℝ)≤1:=by
  rw [NativeClock.time_coe]
  apply (div_le_one NativeHeatObservation.timeScale_pos).mpr
  have hp:=Real.pi_gt_three
  unfold NativeHeatObservation.timeScale
  nlinarith

theorem time_pos(hH:0<H):0<NativeClock.time H:=by
  change (0:ℝ)<(NativeClock.time H:ℝ)
  rw [NativeClock.time_coe]
  exact div_pos (show (0:ℝ)<H from hH) NativeHeatObservation.timeScale_pos

/-- The supplied native integral is only recast along two exact clock
identities; no integral map or selected driver is replaced. -/
def native (I:StandardTerminalIto (C:=C) (E:=E) 𝓕 Q H):
    StandardTerminalIto (C:=C) (E:=E)
      (filtration (base 𝓕) (clock rate rp)) Q (rate*NativeClock.time H):=by
  rw [filtration_eq,span_eq]
  exact I

theorem native_heq (I:StandardTerminalIto (C:=C) (E:=E) 𝓕 Q H):
    HEq (native 𝓕 Q H I) I:=by
  unfold native
  exact (cast_heq _ _).trans (cast_heq _ I)

def unit (I:StandardTerminalIto (C:=C) (E:=E) 𝓕 Q H):
    StandardTerminalIto (C:=C) (E:=E) (base 𝓕) Q (NativeClock.time H):=
  inverseIntegral (base 𝓕) Q rate rp (NativeClock.time H) (native 𝓕 Q H I)

def solution_cast
    {F G:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{T S:ℝ≥0}(hF:F=G)(hT:T=S)
    (κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a){ell M:ℝ}
    (hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)
    (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) F Q T)
    (J0 J1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) G Q S)
    (h0:HEq I0 J0)(h1:HEq I1 J1)(u₀:StateL2)
    (A:NativeMildFirst.Data F Q T κ hκ ha hell hb I0 I1 u₀):
    NativeMildFirst.Data G Q S κ hκ ha hell hb J0 J1 u₀:=by
  subst G
  subst S
  cases eq_of_heq h0
  cases eq_of_heq h1
  exact A

theorem solution_cast_value
    {F G:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{T S:ℝ≥0}(hF:F=G)(hT:T=S)
    (κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a){ell M:ℝ}
    (hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)
    (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) F Q T)
    (J0 J1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) G Q S)
    (h0:HEq I0 J0)(h1:HEq I1 J1)(u₀:StateL2)
    (A:NativeMildFirst.Data F Q T κ hκ ha hell hb I0 I1 u₀):
    (solution_cast Q hF hT κ hκ ha hell hb I0 I1 J0 J1 h0 h1 u₀ A).value=A.value:=by
  subst G
  subst S
  cases eq_of_heq h0
  cases eq_of_heq h1
  rfl

theorem bdg_cast
    {F G:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{T S:ℝ≥0}(hF:F=G)(hT:T=S)
    (I:StandardTerminalIto (C:=C) (E:=E) F Q T)
    (J:StandardTerminalIto (C:=C) (E:=E) G Q S)(hI:HEq I J)
    (B:ℝ≥0)(hB:StandardTerminalBDG16 I B):StandardTerminalBDG16 J B:=by
  subst G
  subst S
  cases eq_of_heq hI
  exact hB

/-- Any actual smooth inverse-clock model returns a native mild
solution on the ORIGINAL filtration, horizon and selected integrals. -/
def solution
    (κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a){ell M K β:ℝ}
    (hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hK:0≤K)
    (hholder:∀z w,|a z-a w|≤K*|z-w|^β)
    (I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 Q H)
    (u₀:StateL2)(hH:(H:ℝ)≤1)
    (A:NativeSmoothFirstConstruction.Model (base 𝓕) Q (NativeClock.time H) (time_le_one H hH)
      κ hκ ha hell hb hβ hK hholder (fun b=>unit 𝓕 Q H (I b)) u₀):
    NativeMildFirst.Data 𝓕 Q H κ hκ ha hell hb (I true) (I false) u₀:=by
  have hN:=NativeSmoothFirstConstruction.native (base 𝓕) Q (NativeClock.time H)
    (time_le_one H hH) κ hκ ha hell hb hβ hK hholder
      (fun b=>unit 𝓕 Q H (I b)) u₀ A
  have h0:HEq (integral (base 𝓕) Q rate rp (NativeClock.time H) (unit 𝓕 Q H (I true))) (I true):=
    (heq_of_eq (integral_inverseIntegral_eq (base 𝓕) Q rate rp (NativeClock.time H)
      (native 𝓕 Q H (I true)))).trans (native_heq 𝓕 Q H (I true))
  have h1:HEq (integral (base 𝓕) Q rate rp (NativeClock.time H) (unit 𝓕 Q H (I false))) (I false):=
    (heq_of_eq (integral_inverseIntegral_eq (base 𝓕) Q rate rp (NativeClock.time H)
      (native 𝓕 Q H (I false)))).trans (native_heq 𝓕 Q H (I false))
  exact solution_cast Q (filtration_eq 𝓕) (span_eq H) κ hκ ha hell hb
    _ _ (I true) (I false) h0 h1 u₀ hN

theorem solution_value
    (κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a){ell M K β:ℝ}
    (hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hK:0≤K)
    (hholder:∀z w,|a z-a w|≤K*|z-w|^β)
    (I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 Q H)
    (u₀:StateL2)(hH:(H:ℝ)≤1)
    (A:NativeSmoothFirstConstruction.Model (base 𝓕) Q (NativeClock.time H) (time_le_one H hH)
      κ hκ ha hell hb hβ hK hholder (fun b=>unit 𝓕 Q H (I b)) u₀):
    (solution 𝓕 Q H κ hκ ha hell hb hβ hK hholder I u₀ hH A).value=
      NativePairClock.path A.model.value:=by
  dsimp only [solution,unit]
  rw [solution_cast_value]
  rfl
end SHE.NativeInverseClock
