module

public import SHE.ControlledScalarCovarianceTail
public import SHE.ControlledReferenceWindows

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ControlledScalarCovarianceTailEnergy
open Set MeasureTheory AddCircle StoppedFourier WordRecursion ProfileVariance ProfileL2
  ControlledProfile ProfileStability ControlledScalarCovarianceTail
open scoped NNReal
local instance tailEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance tailEnergy_circleSigma : MeasurableSpace CircleL2:=borel _
local instance tailEnergy_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
attribute [local irreducible] ControlledProfile.profile ControlledReferenceWindows.coefficient

variable (P:CanonicalCovariance.ProfileParameters)

/-- Borel extension of the literal remaining covariance. It agrees
with the actual tail whenever q is before the terminal time. -/
def field (Λ v b θ:ℝ) (p:(Inputs×ℝ)×HeatCircle):ℝ:=
  tail P Λ v (min p.1.2 b) b θ p.1.1.1 p.1.1.2 p.2

theorem field_measurable (Λ v b θ:ℝ):Measurable (field P Λ v b θ):=by
  let Z:VariableObservations.Family ((Inputs×ℝ)×HeatCircle) 1:={
    observations:=fun p=>ScalarCovarianceTailScale.observation b p.2
    stop_measurable:=fun _=>measurable_const
    target_measurable:=fun _=>measurable_const
    center_measurable:=fun _=>measurable_snd}
  have hmap:Measurable (fun p:(((Inputs×ℝ)×HeatCircle)×Domain)=>(p.1.1.1,p.2)):=
    measurable_fst.fst.fst.prodMk measurable_snd
  have hc:Measurable (fun p:(((Inputs×ℝ)×HeatCircle)×Domain)=>
      ControlledReferenceWindows.coefficient P Λ θ v p.1.1.1 p.2):=
    (ControlledReferenceWindows.coefficient_measurable P Λ θ v).comp hmap
  have hm:=Z.covariance_measurable hc
    ((measurable_fst.snd).min measurable_const) measurable_const (fun p=>min_le_right p.1.2 b)
  convert! hm.eval_matrix (i:=0) (j:=0) using 1
  funext p
  unfold field tail ControlledReferenceWindows.coefficient
  rfl

/-- Every actual tail is bounded at its genuine sqrt(future-age) scale. -/
theorem tail_abs_bound {Λ v q b:ℝ} (hqb:q<b) (hage:b-q≤1)
    (θ:ℝ) (u d:CircleL2) (x:HeatCircle):
    |tail P Λ v q b θ u d x|≤upperConstant*P.upper*(b-q)^(1/2:ℝ):=by
  have hc:Measurable (fun p:Domain=>profile P Λ u d (θ,(p.1-v,p.2))):=
    (ControlledProfile.profile_measurable P Λ u d).comp
      (measurable_const.prodMk ((measurable_fst.sub_const v).prodMk measurable_snd))
  have hh:=ScalarCovarianceTailScale.elliptic hc hqb hage P.lower_pos.le P.upper_nonneg
    (fun p=>ControlledProfile.profile_bounds P Λ u d _) x
  have h0:0≤lowerConstant*P.lower*(b-q)^(1/2:ℝ):=by
    exact mul_nonneg (mul_nonneg lowerConstant_pos.le P.lower_pos.le)
      (Real.rpow_nonneg (sub_pos.mpr hqb).le _)
  unfold tail
  rw [abs_of_nonneg (h0.trans hh.1)]
  exact hh.2

variable {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsProbabilityMeasure μ]

/-- The TRUE random-past remaining covariance has original sample/spatial
L2 bounded by original past energy, with both initial and future clocks.
The integrability and Borel hypotheses are derived for the actual tail. -/
theorem actual_energy {Λ v q b:ℝ} (hΛ:0≤Λ) (hvq:v<q) (hqb:q<b)
    (hspan:b-v≤P.horizon)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (u d:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d)
    (hi:Integrable (fun ω=>‖d ω‖^2) μ) (θ η:ℝ):
    let Diff:=fun p:Ω×HeatCircle=>tail P Λ v q b θ (u p.1) (d p.1) p.2-
      tail P Λ v q b η (u p.1) (d p.1) p.2
    Integrable (fun p=>Diff p^2) (μ.prod haarAddCircle) ∧
      (∫p,Diff p^2 ∂μ.prod haarAddCircle)≤
        (constant P)^2*|θ-η|^2*(q-v)^((P.exponent-1)/2)*(b-q)*
          (∫ω,‖d ω‖^2 ∂μ):=by
  intro Diff
  have hmap:Measurable (fun p:Ω×HeatCircle=>(((u p.1,d p.1),q),p.2)):=
    (((hu.comp measurable_fst).prodMk (hd.comp measurable_fst)).prodMk measurable_const).prodMk measurable_snd
  have hm:Measurable Diff:=by
    have h0:=(field_measurable P Λ v b θ).comp hmap
    have h1:=(field_measurable P Λ v b η).comp hmap
    convert! h0.sub h1 using 1
    ext p
    simp only [Diff,field,Function.comp_def,Pi.sub_apply,min_eq_left hqb.le]
  let B:=upperConstant*P.upper*(b-q)^(1/2:ℝ)
  have hbound:∀p:Ω×HeatCircle,|Diff p|≤2*B:=by
    intro p
    have ht0:=tail_abs_bound P (Λ:=Λ) (v:=v) hqb (by linarith [P.horizon_le_one]) θ (u p.1) (d p.1) p.2
    have ht1:=tail_abs_bound P (Λ:=Λ) (v:=v) hqb (by linarith [P.horizon_le_one]) η (u p.1) (d p.1) p.2
    exact (abs_sub _ _).trans (by dsimp only [B];linarith)
  have hmem:MemLp Diff 2 (μ.prod haarAddCircle):=bounded_memLp hm hbound
  have hI:=hmem.integrable_sq
  let K:=(constant P)^2*|θ-η|^2*(q-v)^((P.exponent-1)/2)*(b-q)
  have hK:0≤K:=by dsimp only [K];positivity [sub_pos.mpr hqb]
  have hp:∀ω,(∫x,Diff (ω,x)^2 ∂haarAddCircle)≤K*‖d ω‖^2:=by
    intro ω
    have ht:=tail_difference P hΛ hvq hqb hspan hsmall (u ω) (d ω) θ η
    have hs:=pow_le_pow_left₀ (normTwo_nonneg _ _) ht 2
    rw [normTwo_sq] at hs
    have ha:((q-v)^((P.exponent-1)/4))^2=(q-v)^((P.exponent-1)/2):=by
      rw [←Real.rpow_mul_natCast (sub_pos.mpr hvq).le]
      congr 1
      ring
    have hb:((b-q)^(1/2:ℝ))^2=b-q:=by
      rw [←Real.rpow_mul_natCast (sub_pos.mpr hqb).le]
      norm_num
    simp only [mul_pow,ha,hb] at hs
    convert hs using 1 <;> dsimp only [Diff,K] <;> ring
  refine ⟨hI,?_⟩
  rw [integral_prod _ hI]
  calc
    _≤∫ω,K*‖d ω‖^2 ∂μ:=integral_mono hI.integral_prod_left (hi.const_mul K) hp
    _=K*(∫ω,‖d ω‖^2 ∂μ):=integral_const_mul _ _

end SHE.ControlledScalarCovarianceTailEnergy
