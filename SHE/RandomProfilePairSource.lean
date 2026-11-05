module

public import SHE.HolderRandomScoreEnergy
public import SHE.PastWeightedSpatialEnergy
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section
namespace SHE.RandomProfilePairSource
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2 ProfileStability
  ControlledProfile ControlledResidualScoreInput
open scoped ENNReal
local instance randomProfilePairSource_periodPositive : Fact (0<2*π):=⟨by positivity⟩
local instance randomProfilePairSource_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
variable {W:Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- Actual random-past OWN-baseline differences provide the paired
empty-leaf source with true L² energy to power chi, without a remaining
age loss. The Gaussian/current word may remain correlated with it. -/
theorem energy (P:CanonicalCovariance.ProfileParameters) {Λ:ℝ} (hΛ:0≤Λ)
    (u d:W→CircleL2) (hu:Measurable u) (hd:Measurable d)
    (hsmall:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ:Measure W) [IsProbabilityMeasure μ] (hdi:Integrable (fun ω=>‖d ω‖^2) μ)
    (θ η:ℝ) {r χ:ℝ} (hr:r∈Ioc 0 P.horizon) (hχ:0≤χ) (hχβ:χ≤P.exponent):
    let e:=fun y:W×HeatCircle=>profile P Λ (u y.1) (d y.1) (θ,(r,y.2))-
      profile P Λ (u y.1) (d y.1) (η,(r,y.2))
    Integrable (fun y=>(|e y|^(χ/P.exponent))^2) (μ.prod haarAddCircle) ∧
      (∫y,(|e y|^(χ/P.exponent))^2 ∂μ.prod haarAddCircle)≤
        (2*P.holder*|θ-η|^P.exponent)^(2*χ/P.exponent)*(∫ω,‖d ω‖^2 ∂μ)^χ := by
  intro e
  let C:=2*P.holder*|θ-η|^P.exponent
  have hC:0≤C:=mul_nonneg (mul_nonneg (by norm_num) P.holder_nonneg) (rpow_nonneg (abs_nonneg _) _)
  have he:Measurable e:=by
    have hp(a:ℝ):Measurable (fun y:W×HeatCircle=>((y.1,a),(r,y.2))):=
      (measurable_fst.prodMk measurable_const).prodMk (measurable_const.prodMk measurable_snd)
    convert! ((random_profile_measurable P hu hd Λ).comp (hp θ)).sub
      ((random_profile_measurable P hu hd Λ).comp (hp η)) using 1
  have hf:=FractionalNormEnergy.fractional_square d hd.aestronglyMeasurable hdi
    P.exponent_pos.le P.exponent_le_one
  have hsec:∀ᵐ ω ∂μ,Integrable (fun x:HeatCircle=>‖e (ω,x)‖^2) haarAddCircle ∧
      (∫x:HeatCircle,‖e (ω,x)‖^2 ∂haarAddCircle)≤C^2*‖d ω‖^((2:ℝ)*P.exponent):=by
    apply ae_of_all
    intro ω
    have hm:Measurable (fun x:HeatCircle=>e (ω,x)):=he.comp (measurable_const.prodMk measurable_id)
    have hmem:MemLp (fun x:HeatCircle=>e (ω,x)) 2 haarAddCircle:=bounded_memLp (C:=2*P.upper) hm (fun x=>by
      apply (abs_sub _ _).trans
      have hb(a:ℝ):|profile P Λ (u ω) (d ω) (a,(r,x))|≤P.upper:=by
        rw [abs_of_nonneg (P.lower_pos.le.trans (profile_bounds P Λ (u ω) (d ω) _).1)]
        exact (profile_bounds P Λ (u ω) (d ω) _).2
      exact (add_le_add (hb θ) (hb η)).trans_eq (by ring))
    have hb:=profile_l2_holder P hΛ (u ω) (d ω) θ η hsmall hr
    have hs:=pow_le_pow_left₀ (normTwo_nonneg haarAddCircle _) hb 2
    rw [normTwo_sq] at hs
    have hc:2*(P.holder*(|θ-η| * ‖d ω‖)^P.exponent)=C*‖d ω‖^P.exponent:=by
      rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
      unfold C
      ring
    rw [hc,mul_pow,←Real.rpow_mul_natCast (norm_nonneg _)] at hs
    refine ⟨hmem.norm.integrable_sq,?_⟩
    convert! hs using 1 <;> first |simp only [Real.norm_eq_abs,sq_abs,e]|congr 2 <;> ring
  have hprod:=SectionEnergy.product_energy haarAddCircle μ e he
    (fun ω=>C^2*‖d ω‖^((2:ℝ)*P.exponent)) (hf.1.const_mul _)
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  have hei:Integrable (fun y=>‖e y‖^2) (μ.prod haarAddCircle):=hprod.1
  have heb:(∫y,‖e y‖^2 ∂μ.prod haarAddCircle)≤C^2*(∫ω,‖d ω‖^2 ∂μ)^P.exponent:=by
    apply hprod.2.trans
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hf.2 (sq_nonneg _)
  have hδ:0≤χ/P.exponent:=div_nonneg hχ P.exponent_pos.le
  have hδ1:χ/P.exponent≤1:=(div_le_one P.exponent_pos).mpr hχβ
  have hh:=FractionalNormEnergy.fractional_square e he.aestronglyMeasurable hei hδ hδ1
  have htarget:(C^2*(∫ω,‖d ω‖^2 ∂μ)^P.exponent)^(χ/P.exponent)=
      C^(2*χ/P.exponent)*(∫ω,‖d ω‖^2 ∂μ)^χ := by
    rw [Real.mul_rpow (sq_nonneg _) (rpow_nonneg (integral_nonneg (fun _=>sq_nonneg _)) _),
      ←Real.rpow_natCast_mul hC 2,←Real.rpow_mul (integral_nonneg (fun _=>sq_nonneg _))]
    have hx:P.exponent*(χ/P.exponent)=χ:=by field_simp [P.exponent_pos.ne']
    rw [hx]
    congr 1
    ring
  have hb:=hh.2.trans ((rpow_le_rpow (integral_nonneg (fun _=>sq_nonneg _)) heb hδ).trans_eq htarget)
  have hp(y:W×HeatCircle):(|e y|^(χ/P.exponent))^2=‖e y‖^((2:ℝ)*(χ/P.exponent)):=by
    rw [←Real.rpow_mul_natCast (abs_nonneg _) ]
    simp only [Real.norm_eq_abs]
    congr 1
    ring
  simpa only [hp,C] using And.intro hh.1 hb

end SHE.RandomProfilePairSource
