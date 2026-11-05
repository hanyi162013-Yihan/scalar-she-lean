module

public import SHE.NativeAssignedLeafMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace SHE.BoundedEmptyAssignedLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier
open scoped BigOperators NNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n r k : ℕ}

def leafConstant (P:CanonicalCovariance.ProfileParameters)(b:ℕ)
    (choices:List (Fin r×Fin k))(factor:Fin k):ℝ:=
  if block choices factor=[] then 1 else GaussianAudit.gaussianAbsMoment (((2*b:ℕ):ℝ)*P.exponent)
def leafScale (P:CanonicalCovariance.ProfileParameters)
    (choices:List (Fin r×Fin k))(factor:Fin k)(lo hi:Fin r→ℝ)(age:ℝ)
    (chosen:block choices factor≠[]→Fin r):ℝ:=
  if block choices factor=[] then 2*P.upper
  else NativeAssignedLeafMoments.leafScale P choices factor lo hi age chosen

theorem leafConstant_nonneg (P:CanonicalCovariance.ProfileParameters)(b:ℕ)
    (choices:List (Fin r×Fin k))(factor:Fin k):0≤leafConstant P b choices factor:=by
  unfold leafConstant
  split_ifs
  · norm_num
  · exact GaussianAudit.gaussianAbsMoment_nonneg _

/-- Empty rough factors use their literal bounded cap, uniformly in
every untouched current mean. Nonempty old blocks retain the original
Gaussian minimum-gap gain and the full original profile baseline. -/
theorem even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2) (θ : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j)
    (hlohi : ∀ j,lo j<hi j) (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    (mean : Ω→State n) (hm : Measurable mean) (i : Fin n)
    (hnative : σ i=target i) (ht : target i∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (chosen : block choices factor≠[]→Fin r) (hchosen : ∀ h,chosen h∈block choices factor)
    (b : ℕ) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let F := fun z : Ω×((Fin r→State n)×State n) =>
      ControlledAssignedLeaf.leaf choices factor P.coefficient (mean z.1) i
        (ControlledProfile.profile P Λ u d (θ,(target i,center i))) z.2
    Integrable (fun z => |F z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|F z|^(2*b) ∂μ.prod νG)≤leafConstant P b choices factor*
        (leafScale P choices factor lo hi (target i) chosen)^(2*b) := by
  intro A B νG F
  have hFm:Measurable F:=ParametricAssignedMoments.leaf_measurable choices factor
    P.coefficient P.measurable mean hm i _
  by_cases hblock:block choices factor=[]
  · have hbound(z:Ω×((Fin r→State n)×State n)):|F z|≤2*P.upper:=by
      rw [show F z=ControlledAssignedLeaf.leaf choices factor P.coefficient (mean z.1) i
        (ControlledProfile.profile P Λ u d (θ,(target i,center i))) z.2 from rfl,
        ControlledAssignedLeaf.leaf_empty choices factor hblock]
      have hbase:=ControlledProfile.profile_bounds P Λ u d (θ,(target i,center i))
      have hcoef(z:ℝ):|P.coefficient z|≤P.upper:=by
        rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
        exact P.upper_bound z
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg (P.lower_pos.le.trans hbase.1)]
        linarith [hcoef (mean z.1 i+((∑j,suppress (suppressed choices factor) z.2.1 j)+z.2.2) i),hbase.2])
    have hp:∀z:Ω×((Fin r→State n)×State n),|F z|^(2*b)≤(2*P.upper)^(2*b):=
      fun z=>pow_le_pow_left₀ (abs_nonneg _) (hbound z) _
    have hiF:Integrable (fun z=>|F z|^(2*b)) (μ.prod νG):=
      (integrable_const ((2*P.upper)^(2*b))).mono'
        ((continuous_abs.measurable.comp hFm).pow_const _).aestronglyMeasurable
        (ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hp z))
    refine ⟨hiF,?_⟩
    have hh:=integral_mono hiF (integrable_const ((2*P.upper)^(2*b))) hp
    simpa only [leafConstant,leafScale,hblock,ite_true,one_mul,integral_const,probReal_univ,one_smul] using hh
  · have hfiber (ω : Ω) := WindowAssignedFactors.leaf_even_moment P Λ u d θ lo hi hdisjoint
      σ target center hσ hσ1 hages hq hlo hlohi hstop (mean ω) i hnative ht choices hnd factor chosen hchosen b
    have hf : Measurable F := ParametricAssignedMoments.leaf_measurable choices factor
      P.coefficient P.measurable mean hm i _
    have hh := UniformFiberMoments.even_moment μ νG F hf b
      (GaussianAudit.gaussianAbsMoment (((2*b:ℕ):ℝ)*P.exponent)*
        (leafScale P choices factor lo hi (target i) chosen)^(2*b))
      (fun ω => (hfiber ω).1) (fun ω => by
        have hhb := (hfiber ω).2
        simp only [WindowAssignedFactors.leafConstant,WindowAssignedFactors.leafScale,
          leafScale,NativeAssignedLeafMoments.leafScale,hblock,ite_false,dite_false] at hhb ⊢
        convert! hhb using 1)
    simpa only [leafConstant,hblock,ite_false] using hh

end SHE.BoundedEmptyAssignedLeaf
