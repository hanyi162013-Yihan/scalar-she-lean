module

public import SHE.VariableScoreInput
public import SHE.HeatForestProduct

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ForestedScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 StoppedScoreLeverage StoppedCovarianceInput OrderedHeatForests
local instance forestedScoreInput_periodPos : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {n : ℕ} {W : Type*} [MeasurableSpace W]

/-- Positive averaging of the whole stopped score input preserves its
sharp spatial L2 rate. The coarse rate is used only to justify Fubini. -/
theorem averaged_input_normTwo (μ : Measure W) [SFinite μ]
    (K : W→ℝ) (hKm : Measurable K) (hKi : Integrable K μ) (hK : ∀ w,0≤K w)
    (σ target : Fin n→ℝ) (center : W→Fin n→HeatCircle) (hcenter : Measurable center)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {s α τ ell U A B : ℝ} (hs : 0<s) (hα : -1<α) (hα0 : α≤0)
    (hτ : -1<τ) (hτ0 : τ<0) (hell : 0<ell) (hA : 0≤A) (hB : 0≤B)
    (hstop : ∀ i,s≤σ i) (c e : Domain→ℝ) (hc : Measurable c) (he : Measurable e)
    (hcb : ∀ p,0≤c p ∧ c p≤U) (hcl : ∀ p,ell≤c p)
    (hcoarse : ∀ p,0≤p.1 → |e p|≤B*p.1^τ)
    (hsharp : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),normTwo haarAddCircle (fun x=>e (r,x))≤A*r^α) :
    normTwo haarAddCircle (fun x=>∫ w,K w*scoreInput σ target (center w) c e x ∂μ)≤
      (∫ w,K w ∂μ)*(A*(((n:ℝ)/ell)*(s/2)^α*(1+2/(α+1)))) := by
  let a := A*(((n:ℝ)/ell)*(s/2)^α*(1+2/(α+1)))
  let b := B*((n:ℝ)/ell)*(s/2)^τ*(1+2/(τ+1))
  have ha : 0≤a := by dsimp only [a];positivity [show 0<α+1 by linarith]
  have hb : 0≤b := by dsimp only [b];positivity [show 0<τ+1 by linarith]
  have hGm := scoreInput_variable_centers_measurable σ target center hcenter c e hc he
  have hG0 (w : W) (x : HeatCircle) : 0≤scoreInput σ target (center w) c e x :=
    scoreInput_nonneg σ target (center w) hσ hσ1 hages c hc U ell hcb hell hcl e x
  have hGb (w : W) (x : HeatCircle) : scoreInput σ target (center w) c e x≤b :=
    (score_input_weighted_bound σ target (fun i=>center w i+x) hσ hσ1 hages hs hτ hτ0 hB hstop
      c hc U ell hcb hell hcl e he hcoarse).2
  have hGw (w : W) : Measurable (scoreInput σ target (center w) c e) := by
    have hpair : Measurable (fun x : HeatCircle=>(w,x)) := measurable_const.prodMk measurable_id
    convert! hGm.comp hpair using 1
  have hGL (w : W) : MemLp (scoreInput σ target (center w) c e) 2 haarAddCircle :=
    bounded_memLp (hGw w) (fun x=>by rw [abs_of_nonneg (hG0 w x)];exact hGb w x)
  have hGa (w : W) : normTwo haarAddCircle (scoreInput σ target (center w) c e)≤a :=
    scoreInput_normTwo_bound σ target (center w) hσ hσ1 hages hs hα hα0 hτ hτ0 hell hA hB hstop
      c hc U hcb hcl e he hcoarse hsharp (hGw w)
  have hh := bounded_minkowski_two
    ((hKm.comp measurable_fst).mul hGm) (hKi.mul_const a) (hKi.mul_const b)
    (ae_of_all _ (fun w=>mul_nonneg (hK w) ha))
    (ae_of_all _ (fun w=>mul_nonneg (hK w) hb))
    (ae_of_all _ (fun w x=>by
      change |K w*scoreInput σ target (center w) c e x|≤K w*b
      rw [abs_of_nonneg (mul_nonneg (hK w) (hG0 w x))]
      exact mul_le_mul_of_nonneg_left (hGb w x) (hK w)))
    (ae_of_all _ (fun w=>by
      change normTwo haarAddCircle (fun x=>K w*scoreInput σ target (center w) c e x)≤K w*a
      rw [normTwo_const_mul (hGL w) (K w),abs_of_nonneg (hK w)]
      exact mul_le_mul_of_nonneg_left (hGa w) (hK w)))
  simpa only [integral_mul_const,Function.comp_apply,Pi.mul_apply,a] using hh

/-- Every original ordered heat forest has mass one. Hence integrating
all old relative locations costs no extra small-time or spatial factor. -/
theorem forest_input_normTwo {m k : ℕ} (T : Forest m k) (aRoot : Fin m→HeatCircle)
    (σ target : Fin (m+k)→ℝ)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {s α τ ell U A B : ℝ} (hs : 0<s) (hα : -1<α) (hα0 : α≤0)
    (hτ : -1<τ) (hτ0 : τ<0) (hell : 0<ell) (hA : 0≤A) (hB : 0≤B)
    (hstop : ∀ i,s≤σ i) (c e : Domain→ℝ) (hc : Measurable c) (he : Measurable e)
    (hcb : ∀ p,0≤c p ∧ c p≤U) (hcl : ∀ p,ell≤c p)
    (hcoarse : ∀ p,0≤p.1 → |e p|≤B*p.1^τ)
    (hsharp : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),normTwo haarAddCircle (fun x=>e (r,x))≤A*r^α) :
    normTwo haarAddCircle (fun x=>∫ w : Fin k→HeatCircle,
      density T (values aRoot k w)*scoreInput σ target (values aRoot k w) c e x
        ∂Measure.pi (fun _=>haarAddCircle))≤
      A*(((m+k:ℕ):ℝ)/ell*(s/2)^α*(1+2/(α+1))) := by
  have hKc := (density_continuous T).comp (values_continuous aRoot k)
  have hKi : Integrable (fun w : Fin k→HeatCircle=>density T (values aRoot k w))
      (Measure.pi (fun _=>haarAddCircle)) :=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass : (∫ w : Fin k→HeatCircle,density T (values aRoot k w)
      ∂Measure.pi (fun _=>haarAddCircle))=1 := by
    simpa only [average_const,mul_one] using
      (average_eq_integral_continuous T (fun _=>1) continuous_const aRoot).symm
  have hh := averaged_input_normTwo (Measure.pi (fun _ : Fin k=>haarAddCircle))
    (fun w=>density T (values aRoot k w)) hKc.measurable hKi
    (fun w=>density_nonneg T (values aRoot k w)) σ target (values aRoot k)
    (values_continuous aRoot k).measurable hσ hσ1 hages hs hα hα0 hτ hτ0 hell hA hB hstop
    c e hc he hcb hcl hcoarse hsharp
  simpa only [hmass,one_mul] using hh

end SHE.ForestedScoreInput
