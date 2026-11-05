module

public import SHE.OffsetAssignedLeafMoments
public import SHE.TwoProfileWindowLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace SHE.TwoProfileAssignedLeaf
open OffsetAssignedLeafMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier
open scoped BigOperators NNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n r k : ℕ}

/-- A scalar current-mean displacement moment is sufficient for the
whole suppressed rough factor. It is measured against the genuine
FULL-profile mean/baseline; the reduced Gaussian law never replaces
that baseline. This theorem is independent of a choice of stochastic
coefficient or a particular coupling of current states. -/
theorem even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2) (θ η : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j)
    (hlohi : ∀ j,lo j<hi j) (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    (mean : Ω→State n) (hm : Measurable mean) (i : Fin n)
    (hnative : σ i=target i) (ht : target i∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (chosen : block choices factor≠[]→Fin r) (hchosen : ∀ h,chosen h∈block choices factor)
    (b : ℕ) (C0 : ℝ)
    (hoffset : Integrable (fun ω => |mean ω i-ControlledProfile.mean Λ u d (η,(target i,center i))|^
      (((2*b:ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω i-ControlledProfile.mean Λ u d (η,(target i,center i))|^
        (((2*b:ℕ):ℝ)*P.exponent) ∂μ)≤C0*(target i)^((b:ℝ)*P.exponent/2)) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let F := fun z : Ω×((Fin r→State n)×State n) =>
      ControlledAssignedLeaf.leaf choices factor P.coefficient (mean z.1) i
        (ControlledProfile.profile P Λ u d (η,(target i,center i))) z.2
    Integrable (fun z => |F z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|F z|^(2*b) ∂μ.prod νG)≤leafConstant P b C0 choices factor*
        (NativeAssignedLeafMoments.leafScale P choices factor lo hi (target i) chosen)^(2*b) := by
  intro A B νG F
  have hmean : Measurable (fun ω => mean ω i) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.measurable.comp hm
  by_cases hblock : block choices factor=[]
  · let ref := ControlledProfile.mean Λ u d (η,(target i,center i))
    have hiOffset := (measurePreserving_fst (μ:=μ) (ν:=νG)).integrable_comp_of_integrable hoffset.1
    have heOffset : (∫ z : Ω×((Fin r→State n)×State n),
        |mean z.1 i-ref|^(((2*b:ℕ):ℝ)*P.exponent) ∂μ.prod νG)=
        ∫ ω,|mean ω i-ref|^(((2*b:ℕ):ℝ)*P.exponent) ∂μ := by
      calc
        _=∫ ω,∫ _ : (Fin r→State n)×State n,
            |mean ω i-ref|^(((2*b:ℕ):ℝ)*P.exponent) ∂νG ∂μ := by
          convert! integral_prod _ hiOffset using 1
        _=_ := by simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have hh := TwoProfileWindowLeaf.even_moment μ P Λ u d θ η lo hi hdisjoint
      σ target center hages hq hlo i hnative ht (suppressed choices factor)
      (fun z => mean z.1 i) (hmean.comp measurable_fst) b hiOffset
    have he : F=(fun z : Ω×((Fin r→State n)×State n) =>
        P.coefficient (mean z.1 i+((∑ j,suppress (suppressed choices factor) z.2.1 j)+z.2.2) i)-
          ControlledProfile.profile P Λ u d (η,(target i,center i))) := by
      funext z
      exact ControlledAssignedLeaf.leaf_empty choices factor hblock _ _ _ _ _
    have hez (z : Ω×((Fin r→State n)×State n)) := congrFun he z
    dsimp only at hh
    simp_rw [←hez] at hh
    refine ⟨hh.1,hh.2.trans ?_⟩
    rw [heOffset]
    have htp : (target i)^((b:ℝ)*P.exponent/2)=((target i)^(P.exponent/4))^(2*b) := by
      rw [←Real.rpow_mul_natCast ht.1.le]
      congr 1
      push_cast
      ring
    have hc := mul_le_mul_of_nonneg_left hoffset.2 (pow_nonneg P.holder_nonneg (2*b))
    have hbound := mul_le_mul_of_nonneg_left (add_le_add hc (le_refl
      (GaussianCenteredLeafMoments.leafMomentConstant b P.exponent*
        (P.holder*(ProfileVariance.upperConstant*P.upper)^(P.exponent/2)*
          (target i)^(P.exponent/4))^(2*b))))
      (show 0≤(2:ℝ)^(2*b-1) by positivity)
    refine hbound.trans_eq ?_
    simp only [leafConstant,NativeAssignedLeafMoments.leafScale,hblock,ite_true,dite_true,htp,mul_pow]
    ring
  · have hfiber (ω : Ω) := WindowAssignedFactors.leaf_even_moment P Λ u d θ lo hi hdisjoint
      σ target center hσ hσ1 hages hq hlo hlohi hstop (mean ω) i hnative ht choices hnd factor chosen hchosen b
    have heBaseline (ω : Ω) :
        ControlledAssignedLeaf.leaf choices factor P.coefficient (mean ω) i
          (ControlledProfile.profile P Λ u d (θ,(target i,center i)))=
        ControlledAssignedLeaf.leaf choices factor P.coefficient (mean ω) i
          (ControlledProfile.profile P Λ u d (η,(target i,center i))) := by
      rw [ControlledAssignedLeaf.leaf_nonempty choices factor hblock,
        ControlledAssignedLeaf.leaf_nonempty choices factor hblock]
    have hfiber' (ω : Ω) := hfiber ω
    simp_rw [heBaseline] at hfiber'
    have hf : Measurable F := ParametricAssignedMoments.leaf_measurable choices factor
      P.coefficient P.measurable mean hm i _
    have hh := UniformFiberMoments.even_moment μ νG F hf b
      (GaussianAudit.gaussianAbsMoment (((2*b:ℕ):ℝ)*P.exponent)*
        (NativeAssignedLeafMoments.leafScale P choices factor lo hi (target i) chosen)^(2*b))
      (fun ω => (hfiber' ω).1) (fun ω => by
        have hhb := (hfiber' ω).2
        simp only [WindowAssignedFactors.leafConstant,WindowAssignedFactors.leafScale,
          NativeAssignedLeafMoments.leafScale,hblock,ite_false,dite_false] at hhb ⊢
        convert! hhb using 1)
    simpa only [leafConstant,hblock,ite_false] using hh

end SHE.TwoProfileAssignedLeaf
