module
public import SHE.FiniteHaarColumnProjection
public import SHE.ProcessEnergy
public import SHE.EnergyConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FiniteHaarProjectionL2
open MeasureTheory FiniteHaar HilbertColumns Filter PredictableL2
open scoped ENNReal Topology
variable {X E:Type*}[MeasurableSpace X][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(ν:Measure X)
local instance : Fact ((1:ℝ≥0∞)≤2):=⟨by norm_num⟩
local instance : Fact ((2:ℝ≥0∞)≠⊤):=⟨by norm_num⟩

def projection(F:Finset HaarNode):Lp (Space HaarNode E) 2 ν→L[ℝ] Lp (Space HaarNode E) 2 ν:=
  (FiniteHaarColumnProjection.projection F).compLpL 2 ν

theorem projection_ae(F:Finset HaarNode)(v:Lp (Space HaarNode E) 2 ν) :
    projection ν F v=ᵐ[ν] fun x=>FiniteHaarColumnProjection.projection F (v x) :=
  (FiniteHaarColumnProjection.projection (E:=E) F).coeFn_compLpL v

theorem norm_le(F:Finset HaarNode)(v:Lp (Space HaarNode E) 2 ν):
    ‖projection ν F v‖≤‖v‖:=by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [projection_ae ν F v] with x hx
  rw [hx]
  exact FiniteHaarColumnProjection.norm_le F (v x)

theorem tendsto(v:Lp (Space HaarNode E) 2 ν):
    Tendsto (fun n=>projection ν (nodesBelow n) v) atTop (𝓝 v):=by
  let error:ℕ→ℝ≥0∞:=fun n=>∫⁻x,ENNReal.ofReal
    (‖FiniteHaarColumnProjection.projection (nodesBelow n) (v x)-v x‖^2) ∂ν
  have hfinite:(∫⁻x,ENNReal.ofReal 4*ENNReal.ofReal (‖v x‖^2) ∂ν)≠⊤:=by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))).mp
      ((Lp.memLp v).norm.integrable_sq).2).ne
  have he:Tendsto error atTop (𝓝 0):=by
    have hs:=Lp.stronglyMeasurable v
    have hsm(n:ℕ):StronglyMeasurable (fun x=>FiniteHaarColumnProjection.projection
        (nodesBelow n) (v x)-v x):=
      ((FiniteHaarColumnProjection.projection (nodesBelow n)).continuous.comp_stronglyMeasurable hs).sub hs
    have hd(n:ℕ)(x:X):‖FiniteHaarColumnProjection.projection (nodesBelow n) (v x)-v x‖^2≤4*‖v x‖^2:=by
      have htri:=norm_sub_le (FiniteHaarColumnProjection.projection (nodesBelow n) (v x)) (v x)
      have hproj:=FiniteHaarColumnProjection.norm_le (nodesBelow n) (v x)
      nlinarith [norm_nonneg (FiniteHaarColumnProjection.projection (nodesBelow n) (v x)-v x),
        norm_nonneg (v x)]
    have ht:=tendsto_lintegral_of_dominated_convergence
      (μ:=ν) (fun x=>ENNReal.ofReal 4*ENNReal.ofReal (‖v x‖^2))
      (fun n=>ENNReal.continuous_ofReal.measurable.comp ((hsm n).norm.pow 2).measurable)
      (fun n=>ae_of_all _ (fun x=>by
        change ENNReal.ofReal (‖FiniteHaarColumnProjection.projection (nodesBelow n) (v x)-v x‖^2)≤
          ENNReal.ofReal 4*ENNReal.ofReal (‖v x‖^2)
        rw [←ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤4)]
        exact ENNReal.ofReal_le_ofReal (hd n x))) hfinite
      (ae_of_all _ (fun x=>by
        have hh:=(FiniteHaarColumnProjection.tendsto (v x)).sub_const (v x)
        simpa only [sub_self,norm_zero,zero_pow (by decide:2≠0),ENNReal.ofReal_zero,
          Function.comp_def,Pi.sub_apply,Pi.pow_apply] using
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hh.norm.pow 2)))
    simpa only [error,lintegral_zero,Function.comp_def,Pi.sub_apply,Pi.pow_apply] using ht
  apply KernelEnergyCauchy.tendsto_of_energy_error _ _ error he
  intro n
  have hco:(projection ν (nodesBelow n) v-v)=ᵐ[ν]
      (fun x=>FiniteHaarColumnProjection.projection (nodesBelow n) (v x)-v x):=by
    filter_upwards [Lp.coeFn_sub (projection ν (nodesBelow n) v) v,
      projection_ae ν (nodesBelow n) v] with x hx hy
    rw [hx]
    change projection ν (nodesBelow n) v x-v x=_
    rw [hy]
  apply le_of_eq
  rw [realLp_norm_sq,ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp (projection ν (nodesBelow n) v-v)).norm.integrable_sq)
      (ae_of_all _ (fun _=>sq_nonneg _))]
  exact lintegral_congr_ae (hco.mono (fun x hx=>congrArg (fun z:Space HaarNode E=>ENNReal.ofReal (‖z‖^2)) hx))

theorem diagonal{v:ℕ→Lp (Space HaarNode E) 2 ν}{w:Lp (Space HaarNode E) 2 ν}
    (hv:Tendsto v atTop (𝓝 w)):
    Tendsto (fun n=>projection ν (nodesBelow n) (v n)) atTop (𝓝 w):=by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht:=((tendsto ν w).sub_const w).norm
  have hv':Tendsto (fun n=>‖v n-w‖) atTop (𝓝 0):=by
    simpa only [sub_self,norm_zero] using (hv.sub_const w).norm
  have hb(n:ℕ):‖projection ν (nodesBelow n) (v n)-w‖≤
      ‖v n-w‖+‖projection ν (nodesBelow n) w-w‖:=by
    have hsplit:projection ν (nodesBelow n) (v n)-w=
        projection ν (nodesBelow n) (v n-w)+(projection ν (nodesBelow n) w-w):=by
      rw [map_sub]
      abel
    rw [hsplit]
    have hn : ‖projection ν (nodesBelow n) (v n-w)‖≤‖v n-w‖ :=
      norm_le (E:=E) ν (nodesBelow n) (v n-w)
    exact (norm_add_le _ _).trans (add_le_add hn le_rfl)
  exact squeeze_zero (fun _=>norm_nonneg _) hb
    (by simpa only [sub_self,norm_zero,zero_add] using hv'.add ht)
end SHE.FiniteHaarProjectionL2
