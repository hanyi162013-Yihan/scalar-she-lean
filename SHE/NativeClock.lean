module

public import SHE.TimeDilationEquivalence
public import SHE.NativeHeatObservation
public import SHE.VolterraPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeClock
open MeasureTheory Set PredictableTimeDilation LowBands
open scoped NNReal ENNReal

def rate : ℝ≥0 := ⟨NativeHeatObservation.timeScale,NativeHeatObservation.timeScale_pos.le⟩
theorem rate_pos : 0<rate := NativeHeatObservation.timeScale_pos
theorem rate_coe : (rate:ℝ)=NativeHeatObservation.timeScale := rfl

def time (t : ℝ≥0) : ℝ≥0 := (clock rate rate_pos).symm t

theorem time_coe (t : ℝ≥0) : (time t:ℝ)=(t:ℝ)/NativeHeatObservation.timeScale := by
  change NativeHeatObservation.timeScale⁻¹*(t:ℝ)=_
  ring

theorem real_toNNReal_time (c : ℝ≥0) (hc : 0<c) (s : ℝ) :
    (clock c hc).symm s.toNNReal=(s/(c:ℝ)).toNNReal := by
  change c⁻¹*s.toNNReal=(s/(c:ℝ)).toNNReal
  have he := Real.toNNReal_mul (show 0≤(c:ℝ)⁻¹ from inv_nonneg.mpr c.2) (q := s)
  rw [show (c:ℝ)⁻¹=(c⁻¹:ℝ≥0) by rfl,Real.toNNReal_coe] at he
  simpa only [div_eq_mul_inv,mul_comm,NNReal.coe_inv] using he.symm

theorem heat_time (t : ℝ≥0) : RealHeat.realHeat (time t:ℝ)=NativeHeatObservation.heat (t:ℝ) := by
  rw [time_coe]
  rfl

def volterra (Λ : ℝ) (U : ℝ≥0→StateL2) (t : ℝ≥0) : StateL2 :=
  ∫ s in (0:ℝ)..(t:ℝ),Real.exp (-Λ*((t:ℝ)-s)) • NativeHeatObservation.heat ((t:ℝ)-s) (U s.toNNReal)

/-- The controlled finite-variation term has precisely its physical
coefficient Λ after the same deterministic clock change. -/
theorem volterra_time (Λ : ℝ) (U : ℝ≥0→StateL2) (t : ℝ≥0) :
    ((rate:ℝ)*Λ) • VolterraPath.value ((rate:ℝ)*Λ) U (time t)=
      Λ • volterra Λ (fun s => U (time s)) t := by
  let F : ℝ→StateL2 := fun s => Real.exp (-Λ*((t:ℝ)-s)) •
    NativeHeatObservation.heat ((t:ℝ)-s) (U (((s/NativeHeatObservation.timeScale).toNNReal)))
  have hc := NativeHeatObservation.timeScale_pos
  have hs := intervalIntegral.smul_integral_comp_mul_left (f := F) (a := (0:ℝ))
    (b := (time t:ℝ)) NativeHeatObservation.timeScale
  have hct : NativeHeatObservation.timeScale*(time t:ℝ)=(t:ℝ) := by
    rw [time_coe]
    field_simp [hc.ne']
  rw [mul_zero,hct] at hs
  have heq : (fun s : ℝ => F (NativeHeatObservation.timeScale*s))=
      fun s => Real.exp (-((rate:ℝ)*Λ)*((time t:ℝ)-s)) •
        RealHeat.realHeat ((time t:ℝ)-s) (U s.toNNReal) := by
    funext s
    dsimp only [F,NativeHeatObservation.heat]
    have ha : ((t:ℝ)-NativeHeatObservation.timeScale*s)/NativeHeatObservation.timeScale=(time t:ℝ)-s := by
      rw [time_coe]
      field_simp
      <;> ring
    have hb : -Λ*((t:ℝ)-NativeHeatObservation.timeScale*s)=-((rate:ℝ)*Λ)*((time t:ℝ)-s) := by
      rw [rate_coe,time_coe]
      field_simp
      <;> ring
    rw [ha,hb,mul_div_cancel_left₀ s hc.ne']
  rw [heq] at hs
  have hs' : (rate:ℝ) • VolterraPath.value ((rate:ℝ)*Λ) U (time t)=∫ s in (0:ℝ)..(t:ℝ),F s := hs
  calc
    _=Λ • ((rate:ℝ) • VolterraPath.value ((rate:ℝ)*Λ) U (time t)) := by
      rw [smul_smul]
      exact congrArg (fun r : ℝ => r • VolterraPath.value ((rate:ℝ)*Λ) U (time t)) (mul_comm _ _)
    _=Λ • (∫ s in (0:ℝ)..(t:ℝ),F s) := congrArg (fun v : StateL2 => Λ•v) hs'
    _=_ := ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change F s=Real.exp (-Λ*((t:ℝ)-s)) • NativeHeatObservation.heat ((t:ℝ)-s) (U (time s.toNNReal))
  rw [time,real_toNNReal_time rate rate_pos,rate_coe]

end SHE.NativeClock
