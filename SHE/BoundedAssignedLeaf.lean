module

public import SHE.OffsetAssignedLeafMoments
public import SHE.BoundedWindowLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace SHE.BoundedAssignedLeaf
open OffsetAssignedLeafMoments
open JointGaussianBlocks
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
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (c : Domain→ℝ) (hc : Measurable c) (hcb : ∀ p,P.lower≤c p ∧ c p≤P.upper) (η : ℝ)
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
    let B := stoppedCovariance σ target center (BoundedWindowDecomposition.residual P Λ u d lo hi c) q
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
    have hh := BoundedWindowLeaf.even_moment μ P Λ u d c hc hcb η lo hi hdisjoint
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
  · have hfiber (ω : Ω) := PhysicalJointBlocks.rough_block_even_moment σ target center hσ hσ1 hages _
      (referenceProfile_measurable P Λ u d)
      (fun z=>⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d z).1,
        (referenceProfile_bounds P Λ u d z).2⟩) lo hi (fun j=>hq.trans (hlo j)) hlohi hstop B
      choices hnd factor (chosen hblock) (hchosen hblock) i P.coefficient P.measurable
      P.holder_nonneg P.exponent_pos.le P.holder_bound (fun y=>mean ω i+y i) (by fun_prop) b
    have he (ω : Ω) : (fun z=>F (ω,z))=jointBlock choices factor P.coefficient (fun y=>mean ω i+y i)
        (fun _=>EuclideanSpace.proj (𝕜:=ℝ) i) := by
      change ControlledAssignedLeaf.leaf choices factor P.coefficient (mean ω) i
        (ControlledProfile.profile P Λ u d (η,(target i,center i)))=_
      exact ControlledAssignedLeaf.leaf_nonempty choices factor hblock _ _ _ _
    have hfiber' (ω : Ω) : Integrable (fun z=>|F (ω,z)|^(2*b)) νG ∧
        (∫ z,|F (ω,z)|^(2*b) ∂νG)≤GaussianAudit.gaussianAbsMoment (((2*b:ℕ):ℝ)*P.exponent)*
          (NativeAssignedLeafMoments.leafScale P choices factor lo hi (target i) chosen)^(2*b) := by
      simp_rw [show ∀ z,F (ω,z)=jointBlock choices factor P.coefficient (fun y=>mean ω i+y i)
        (fun _=>EuclideanSpace.proj (𝕜:=ℝ) i) z from fun z=>congrFun (he ω) z]
      simpa only [NativeAssignedLeafMoments.leafScale,hblock,dite_false] using hfiber ω
    have hf : Measurable F := ParametricAssignedMoments.leaf_measurable choices factor
      P.coefficient P.measurable mean hm i _
    have hh:=UniformFiberMoments.even_moment μ νG F hf b
      (GaussianAudit.gaussianAbsMoment (((2*b:ℕ):ℝ)*P.exponent)*
        (NativeAssignedLeafMoments.leafScale P choices factor lo hi (target i) chosen)^(2*b))
      (fun ω=>(hfiber' ω).1) (fun ω=>(hfiber' ω).2)
    simpa only [leafConstant,hblock,ite_false] using hh

end SHE.BoundedAssignedLeaf
