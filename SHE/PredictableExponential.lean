module
public import SHE.PredictableMultiplier
public import SHE.ProcessEnergy
public import SHE.PredictableTime
public import Mathlib.Topology.MetricSpace.Contracting
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.PredictableExponential
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(h:ℝ≥0)

def weight (γ:ℝ)(p:ℝ≥0×Ω):ℝ:=Real.exp (γ*min (p.1:ℝ) (h:ℝ))

theorem predictable (γ:ℝ):StronglyMeasurable[𝓕.predictable] (weight (Ω:=Ω) h γ):=
  (((PredictableClock.real_time_measurable 𝓕).min measurable_const).const_mul γ).exp.stronglyMeasurable

theorem bound (γ:ℝ)(p:ℝ≥0×Ω):|weight h γ p|≤Real.exp (|γ| *(h:ℝ)):=by
  rw [weight,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hτ:0≤min (p.1:ℝ) (h:ℝ):=le_min p.1.2 h.2
  exact (mul_le_mul_of_nonneg_right (le_abs_self γ) hτ).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg γ))

/-- Exponential change of predictable-L2 coordinates on a fixed horizon. -/
def scale (γ:ℝ)(v:Process (E:=E) 𝓕 μ h):Process (E:=E) 𝓕 μ h:=
  PredictableMultiplier.mul 𝓕 μ h (weight h γ) (predictable 𝓕 h γ)
    (Real.exp (|γ| *(h:ℝ))) (bound h γ) v

theorem ae (γ:ℝ)(v:Process (E:=E) 𝓕 μ h):
    scale 𝓕 μ h γ v=ᵐ[energyMeasure μ h](fun p=>weight h γ p • v p):=
  PredictableMultiplier.ae 𝓕 μ h _ _ _ _ v

theorem add (γ:ℝ)(v w:Process (E:=E) 𝓕 μ h):
    scale 𝓕 μ h γ (v+w)=scale 𝓕 μ h γ v+scale 𝓕 μ h γ w:=
  PredictableMultiplier.add 𝓕 μ h _ _ _ _ v w

theorem sub (γ:ℝ)(v w:Process (E:=E) 𝓕 μ h):
    scale 𝓕 μ h γ (v-w)=scale 𝓕 μ h γ v-scale 𝓕 μ h γ w:=
  PredictableMultiplier.sub 𝓕 μ h _ _ _ _ v w

theorem cancel (γ:ℝ)(v:Process (E:=E) 𝓕 μ h):
    scale 𝓕 μ h (-γ) (scale 𝓕 μ h γ v)=v:=by
  apply PredictableMultiplier.inverse
    𝓕 μ h (weight h γ) (predictable 𝓕 h γ) _ (bound h γ)
      (weight h (-γ)) (predictable 𝓕 h (-γ)) _ (bound h (-γ))
  intro p
  simp only [weight]
  rw [←Real.exp_add]
  convert Real.exp_zero using 1 <;> congr 1 <;> ring

theorem cancel' (γ:ℝ)(v:Process (E:=E) 𝓕 μ h):
    scale 𝓕 μ h γ (scale 𝓕 μ h (-γ) v)=v:=by
  simpa only [neg_neg] using cancel 𝓕 μ h (-γ) v

section Energy
variable [SFinite μ]

theorem energy (γ:ℝ)(v:Process (E:=E) 𝓕 μ h):
    ENNReal.ofReal (‖scale 𝓕 μ h γ v‖^2)=
      ∫⁻t,∫⁻ω,ENNReal.ofReal (Real.exp (2*γ*(t:ℝ))*‖v (t,ω)‖^2) ∂μ ∂timeMeasure h:=by
  rw [process_lintegral_energy]
  have hs:=Measure.ae_ae_of_ae_prod (ae 𝓕 μ h γ v)
  apply lintegral_congr_ae
  filter_upwards [hs,timeMeasure_ae_mem h] with t ht htime
  apply lintegral_congr_ae
  filter_upwards [ht] with ω hω
  rw [hω,norm_smul,Real.norm_eq_abs]
  have he:|weight h γ (t,ω)|^2=Real.exp (2*γ*(t:ℝ)):=by
    rw [weight,min_eq_left (by exact_mod_cast htime.2),abs_of_pos (Real.exp_pos _),pow_two,←Real.exp_add]
    congr 1
    ring
  rw [mul_pow,he]
end Energy

section FixedPoint
variable [CompleteSpace E]

def conjugate (γ:ℝ)(forcing:Process (E:=E) 𝓕 μ h)
    (N:Process (E:=E) 𝓕 μ h→Process (E:=E) 𝓕 μ h)(z:Process (E:=E) 𝓕 μ h):Process (E:=E) 𝓕 μ h:=
  scale 𝓕 μ h (-γ) (forcing+N (scale 𝓕 μ h γ z))

/-- A proved weighted contraction constructs the ordinary forced fixed
point on the whole prescribed horizon. This is a purely analytic bridge. -/
theorem exists_unique (γ:ℝ)(forcing:Process (E:=E) 𝓕 μ h)
    (N:Process (E:=E) 𝓕 μ h→Process (E:=E) 𝓕 μ h)
    (hLip:LipschitzWith (1/2) (conjugate 𝓕 μ h γ forcing N)):
    ∃!v:Process (E:=E) 𝓕 μ h,v=forcing+N v:=by
  let Φ:=conjugate 𝓕 μ h γ forcing N
  have hc:ContractingWith (1/2) Φ:=⟨by norm_num,hLip⟩
  let y:=hc.fixedPoint Φ
  let v:=scale 𝓕 μ h γ y
  have hy:y=Φ y:=hc.fixedPoint_isFixedPt.symm
  have hv:v=forcing+N v:=by
    have he:=congrArg (scale 𝓕 μ h γ) hy
    simpa only [Φ,conjugate,cancel',v] using he
  refine ⟨v,hv,?_⟩
  intro w hw
  let z:=scale 𝓕 μ h (-γ) w
  have hz:Φ z=z:=by
    dsimp only [Φ,conjugate,z]
    rw [cancel',←hw]
  have hzy:z=y:=hc.fixedPoint_unique hz
  have he:=congrArg (scale 𝓕 μ h γ) hzy
  simpa only [z,v,cancel'] using he
end FixedPoint
end SHE.PredictableExponential
