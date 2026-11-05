module

public import SHE.NormalizedPairedLeaf
public import SHE.TwoProfileAssignedLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalNormalizedEmptyLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier
  OffsetAssignedLeafMoments
open scoped BigOperators NNReal
local instance physicalNormalizedEmptyLeaf_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n r k : ℕ}

/-- A literal physical empty-block endpoint cap under a DIFFERENT
future profile. All covariance/marginal and old-suppression conditions
are discharged by the real Gaussian interval construction. -/
theorem endpoint_moment
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2) (θ η : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j)
    (hlohi : ∀ j,lo j<hi j) (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (i : Fin n) (hnative : σ i=target i) (ht : target i∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (hblock : block choices factor=[]) (p : ℕ) (C0 : ℝ)
    (hOff : |mean i-ControlledProfile.mean Λ u d (η,(target i,center i))|^(((2*p:ℕ):ℝ)*P.exponent)≤
      C0*(target i)^((p:ℝ)*P.exponent/2)) :
    let A:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let ν:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let G:=ControlledAssignedLeaf.leaf choices factor P.coefficient mean i
      (ControlledProfile.profile P Λ u d (η,(target i,center i)))
    Integrable (fun x=>|G x|^(2*p)) ν ∧
      (∫ x,|G x|^(2*p) ∂ν)≤leafConstant P p C0 choices factor*
        (P.holder*(target i)^(P.exponent/4))^(2*p) := by
  intro A B ν G
  let chosen : block choices factor≠[]→Fin r:=fun h=>(h hblock).elim
  have hch : ∀ h,chosen h∈block choices factor:=fun h=>(h hblock).elim
  have hoff : Integrable (fun _ : Unit=>|mean i-ControlledProfile.mean Λ u d
      (η,(target i,center i))|^(((2*p:ℕ):ℝ)*P.exponent)) (Measure.dirac ()) ∧
      (∫ _ : Unit,|mean i-ControlledProfile.mean Λ u d (η,(target i,center i))|^
        (((2*p:ℕ):ℝ)*P.exponent) ∂Measure.dirac ())≤C0*(target i)^((p:ℝ)*P.exponent/2) := by
    refine ⟨integrable_const _,?_⟩
    simpa only [integral_const,probReal_univ,one_smul] using hOff
  have hh:=TwoProfileAssignedLeaf.even_moment (Measure.dirac ()) P Λ u d θ η
    σ target center hσ hσ1 hages hq lo hi hlo hlohi hstop hdisjoint (fun _ : Unit=>mean)
    measurable_const i hnative ht choices hnd factor chosen hch p C0 hoff
  dsimp only at hh
  have hmap : MeasurePreserving (Prod.mk ()) ν ((Measure.dirac ()).prod ν) :=
    ⟨measurable_const.prodMk measurable_id,(Measure.dirac_prod ()).symm⟩
  have hiG:=hmap.integrable_comp_of_integrable hh.1
  have he:=hmap.hasLaw.integral_comp hh.1.aestronglyMeasurable
  have hbG:=he.trans_le hh.2
  refine ⟨by convert! hiG using 1,?_⟩
  simp only [NativeAssignedLeafMoments.leafScale,hblock,dite_true] at hbG
  convert! hbG using 1

/-- Physical all-even moments of the normalized WHOLE empty paired
leaf. The old Gaussian laws and common future law stay fixed; both
proper endpoint baselines and both true current offsets are retained. -/
theorem even_moment
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2) (θ ηOld ηNew : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j)
    (hlohi : ∀ j,lo j<hi j) (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (newMean oldMean : State n) (i : Fin n) (hnative : σ i=target i) (ht : target i∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (hblock : block choices factor=[]) (p : ℕ)
    {χ C0 C1 : ℝ} (hχ : 0≤χ) (hχβ : χ≤P.exponent) (hC0 : 0≤C0) (hC1 : 0≤C1)
    (hOld : |oldMean i-ControlledProfile.mean Λ u d (ηOld,(target i,center i))|^
      (((2*p:ℕ):ℝ)*P.exponent)≤C0*(target i)^((p:ℝ)*P.exponent/2))
    (hNew : |newMean i-ControlledProfile.mean Λ u d (ηNew,(target i,center i))|^
      (((2*p:ℕ):ℝ)*P.exponent)≤C1*(target i)^((p:ℝ)*P.exponent/2)) :
    let A:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
    let ν:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let noise:=fun x : (Fin r→State n)×State n=>((∑ j,suppress (suppressed choices factor) x.1 j)+x.2) i
    let N:=fun x=>NormalizedPairedLeaf.value P.coefficient P.holder P.exponent χ (newMean i) (oldMean i)
      (ControlledProfile.profile P Λ u d (ηNew,(target i,center i)))
      (ControlledProfile.profile P Λ u d (ηOld,(target i,center i))) (noise x)
    Integrable (fun x=>|N x|^(2*p)) ν ∧
      (∫ x,|N x|^(2*p) ∂ν)≤
        (1+(2:ℝ)^(2*p-1)*(leafConstant P p C0 choices factor+leafConstant P p C1 choices factor))*
          ((P.holder*(target i)^(P.exponent/4))^(1-χ/P.exponent))^(2*p) := by
  intro A B ν noise N
  have ho:=endpoint_moment P Λ u d θ ηOld σ target center hσ hσ1 hages hq lo hi hlo hlohi hstop hdisjoint
    oldMean i hnative ht choices hnd factor hblock p C0 hOld
  have hn:=endpoint_moment P Λ u d θ ηNew σ target center hσ hσ1 hages hq lo hi hlo hlohi hstop hdisjoint
    newMean i hnative ht choices hnd factor hblock p C1 hNew
  dsimp only at ho hn
  simp_rw [ControlledAssignedLeaf.leaf_empty choices factor hblock] at ho hn
  have hnoise : Measurable noise := by
    dsimp [noise]
    simp_rw [SuppressedGaussianLaw.suppress_apply]
    fun_prop
  exact NormalizedPairedLeaf.even_moment ν noise hnoise P.coefficient P.measurable
    P.holder_nonneg P.exponent_pos hχ hχβ P.holder_bound (newMean i) (oldMean i)
    (ControlledProfile.profile P Λ u d (ηNew,(target i,center i)))
    (ControlledProfile.profile P Λ u d (ηOld,(target i,center i))) p
    (leafConstant_nonneg P p hC0 choices factor) (leafConstant_nonneg P p hC1 choices factor)
    (mul_nonneg P.holder_nonneg (rpow_nonneg ht.1.le _)) ho.1 hn.1 ho.2 hn.2

end SHE.PhysicalNormalizedEmptyLeaf
