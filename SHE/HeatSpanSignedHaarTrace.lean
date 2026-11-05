module

public import SHE.HeatProjection
public import SHE.HaarLimit
public import SHE.HaarDamping
public import SHE.FractionalEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.HeatProjection
open MeasureTheory Set Real AddCircle HeatTorus HeatTorusKernel FiniteHaar CircleHeat
open scoped ENNReal
local instance heatSpanSignedHaarTrace_period : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

/-- The actual countable signed Haar factor is projected before taking
absolute values. Spatial translation then cancels the heat trace's
quarter-age loss. No coefficient independence is used. -/
theorem translated_signed_haar_projection (q:ℕ) :
    ∃h C θ:ℝ,0<h ∧ h≤1 ∧ 0<C ∧ 0<θ ∧
      ∀(t:Fin q→ℝ)(a:Fin q→UnitAddCircle),
      (∀i,0<t i)→(∀i,t i≤h)→
      ∀(w A:ℝ),0<w→1≤A→(∀i,w≤t i)→(∀i,t i≤A*w)→θ*w≤1→
      ∀{κ Λ ρ:ℝ},0≤κ→0<Λ→0<ρ→ρ<1/2→
      ∀(f g:CircleHeat.CircleL2)(m U:ℝ),0<m→
      (∀ᵐy∂haarAddCircle,(f y).im=0)→(∀ᵐy∂haarAddCircle,(g y).im=0)→
      (∀ᵐy∂haarAddCircle,m≤(f y).re ∧ (f y).re≤U)→
      (∀ᵐy∂haarAddCircle,m≤(g y).re ∧ (g y).re≤U)→
      let F:=fun j:HaarNode=>fun x:UnitAddCircle=>
        ‖(heatSpan t (fun i=>a i+x)).starProjection (globalSignedColumn j f g)‖^2
      Integrable (fun x=>∑'j,F j x) haarAddCircle ∧
      (∫x,∑'j,F j x ∂haarAddCircle)≤
        C*sqrt A*sqrt w*(signedHeatSqConstant κ ρ m U*
          StepInput.negativeEnergy κ Λ ρ (f-g)*
          (Λ^ρ*(θ*w)^(-(1/2:ℝ))+(θ*w)^(-(1/2:ℝ)-ρ))) := by
  obtain ⟨h,C,θ,hh,hh1,hC,hθ,hproj⟩:=translated_heat_span_projection_bound q
  refine ⟨h,C,θ,hh,hh1,hC,hθ,?_⟩
  intro t a ht hth w A hw hA hlo hhi hθw κ Λ ρ hκ hΛ hρ hρhalf f g m U hm hfreal hgreal hf hg F
  have hheat:=global_signed_heat (mul_pos hθ hw) hθw hκ hΛ hρ hρhalf f g m U hm hfreal hgreal hf hg
  have hFi(j:HaarNode):Integrable (F j) haarAddCircle:=
    (hproj t a ht hth w A hw hA hlo hhi (globalSignedColumn j f g)).1
  have hF0(j:HaarNode)(x:UnitAddCircle):0≤F j x:=sq_nonneg _
  have hb(j:HaarNode):(∫x,F j x ∂haarAddCircle)≤
      (C*sqrt A*sqrt w)*‖heat (θ*w) (globalSignedColumn j f g)‖^2:=
    (hproj t a ht hth w A hw hA hlo hhi (globalSignedColumn j f g)).2
  have hn(j:HaarNode):(∫x,‖F j x‖ ∂haarAddCircle)=(∫x,F j x ∂haarAddCircle):=by
    apply integral_congr_ae
    exact ae_of_all _ (fun x=>Real.norm_of_nonneg (hF0 j x))
  have hs:Summable (fun j:HaarNode=>∫x,‖F j x‖ ∂haarAddCircle):=by
    apply Summable.of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _))
      (fun j=>by rw [hn];exact hb j) (hheat.1.mul_left (C*sqrt A*sqrt w))
  refine ⟨FractionalEnergy.nonnegative_tsum_integrable haarAddCircle F hFi
    (fun j=>ae_of_all _ (hF0 j)) hs,?_⟩
  rw [← integral_tsum_of_summable_integral_norm hFi hs]
  calc
    _≤∑'j:HaarNode,(C*sqrt A*sqrt w)*‖heat (θ*w) (globalSignedColumn j f g)‖^2:=
      (hs.congr hn).tsum_le_tsum hb (hheat.1.mul_left _)
    _=(C*sqrt A*sqrt w)*(∑'j:HaarNode,‖heat (θ*w) (globalSignedColumn j f g)‖^2):=tsum_mul_left
    _≤_:=mul_le_mul_of_nonneg_left hheat.2 (by positivity)

end SHE.HeatProjection
