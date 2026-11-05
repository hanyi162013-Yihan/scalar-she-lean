module

public import SHE.ControlledWindowFiberLeaf
public import SHE.VectorControlledRoot
public import SHE.StoppedAssignedLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.WindowAssignedFactors
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianVectorFractions GaussianCoordinates GaussianCenteredLeafMoments ControlledOldIntervals OldIntervalCovariance
  StoppedGaussianFeatures StoppedFourier ProfileVariance GaussianAudit JointGaussianBlocks
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n d r k : ℕ}

def leafConstant (P : CanonicalCovariance.ProfileParameters) (p : ℕ)
    (choices : List (Fin r×Fin k)) (factor : Fin k) : ℝ :=
  if block choices factor=[] then ControlledWindowFiberLeaf.constant P p
  else gaussianAbsMoment (((2*p:ℕ):ℝ)*P.exponent)

def leafScale (P : CanonicalCovariance.ProfileParameters) (choices : List (Fin r×Fin k)) (factor : Fin k)
    (lo hi : Fin r→ℝ) (age mean ref : ℝ) (chosen : block choices factor≠[]→Fin r) : ℝ :=
  if h : block choices factor=[] then ControlledWindowFiberLeaf.scale P mean ref age
  else (2:ℝ)^((block choices factor).length-1)*P.holder*(upperConstant*(P.lower/2))^(P.exponent/2)*
    (hi (chosen h)-lo (chosen h))^(P.exponent/4)

theorem leafConstant_nonneg (P : CanonicalCovariance.ProfileParameters) (p : ℕ)
    (choices : List (Fin r×Fin k)) (factor : Fin k) : 0≤leafConstant P p choices factor := by
  unfold leafConstant ControlledWindowFiberLeaf.constant
  split_ifs
  · exact mul_nonneg (by positivity) (add_nonneg (by norm_num) (leafMomentConstant_nonneg _ _))
  · exact gaussianAbsMoment_nonneg _

theorem leafScale_nonneg (P : CanonicalCovariance.ProfileParameters)
    (choices : List (Fin r×Fin k)) (factor : Fin k) (lo hi : Fin r→ℝ)
    (hgap : ∀ j,lo j≤hi j) {age : ℝ} (hage : 0≤age) (mean ref : ℝ)
    (chosen : block choices factor≠[]→Fin r) : 0≤leafScale P choices factor lo hi age mean ref chosen := by
  unfold leafScale ControlledWindowFiberLeaf.scale
  split_ifs
  · exact mul_nonneg P.holder_nonneg (add_nonneg (rpow_nonneg (abs_nonneg _) _)
      (mul_nonneg (rpow_nonneg (mul_nonneg upperConstant_pos.le P.upper_nonneg) _) (rpow_nonneg hage _)))
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
      (rpow_nonneg (mul_nonneg upperConstant_pos.le (half_pos P.lower_pos).le) _))
      (rpow_nonneg (sub_nonneg.mpr (hgap _)) _)

/-- Actual assigned rough factors in a genuine future window, at an
arbitrary current mean. Nonempty old blocks keep their original gap;
unassigned factors retain the full reference baseline and mean offset. -/
theorem leaf_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u dir : CircleL2) (θ : ℝ) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i) (mean : State n)
    (coordinate : Fin n) (hnative : σ coordinate=target coordinate)
    (ht : target coordinate∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (chosen : block choices factor≠[]→Fin r) (hchosen : ∀ h,chosen h∈block choices factor) (p : ℕ) :
    let A := familyCovariance σ target center (referenceProfile P Λ u dir) lo hi
    let B := ControlledFixedReserve.covariance P Λ u dir (fixedProfile P Λ u dir lo hi) σ target center q θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)
    let ref := ControlledProfile.mean Λ u dir (θ,(target coordinate,center coordinate))
    let F := ControlledAssignedLeaf.leaf choices factor P.coefficient mean coordinate
      (ControlledProfile.profile P Λ u dir (θ,(target coordinate,center coordinate)))
    Integrable (fun x => |F x|^(2*p)) μ ∧ (∫ x,|F x|^(2*p) ∂μ)≤
      leafConstant P p choices factor*
        (leafScale P choices factor lo hi (target coordinate) (mean coordinate) ref chosen)^(2*p) := by
  intro A B μ ref F
  by_cases hblock : block choices factor=[]
  · have he : F=fun x : (Fin r→State n)×State n =>
        P.coefficient (mean coordinate+((∑ j,suppress (suppressed choices factor) x.1 j)+x.2) coordinate)-
          ControlledProfile.profile P Λ u dir (θ,(target coordinate,center coordinate)) := by
      funext x
      exact ControlledAssignedLeaf.leaf_empty choices factor hblock _ _ _ _ x
    rw [he]
    simpa only [leafConstant,leafScale,hblock,ite_true,dite_true] using
      ControlledWindowFiberLeaf.even_moment P Λ u dir θ lo hi hdisjoint σ target center hages hq hlo
        coordinate hnative ht (suppressed choices factor) (mean coordinate) p
  · rw [show F=jointBlock choices factor P.coefficient (fun y => mean coordinate+y coordinate)
        (fun _ => EuclideanSpace.proj (𝕜:=ℝ) coordinate) from
      ControlledAssignedLeaf.leaf_nonempty choices factor hblock _ _ _ _]
    have hh := PhysicalJointBlocks.rough_block_even_moment σ target center hσ hσ1 hages _
      (referenceProfile_measurable P Λ u dir)
      (fun z => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u dir z).1,
        (referenceProfile_bounds P Λ u dir z).2⟩) lo hi (fun j => hq.trans (hlo j)) hgap hstop B choices hnd factor
      (chosen hblock) (hchosen hblock) coordinate P.coefficient P.measurable P.holder_nonneg
      P.exponent_pos.le P.holder_bound (fun y => mean coordinate+y coordinate) (by fun_prop) p
    simpa only [leafConstant,leafScale,hblock,ite_false,dite_false] using hh

/-- A full smooth root cylinder keeps every old clip in the same actual
future-window law, uniformly over its possibly displaced current mean. -/
theorem root_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u dir : CircleL2) (lo hi : Fin r→ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hlo : ∀ j,0≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (mean : State n) (g : Fin d→Fin n)
    (choices : List (Fin r×Fin k)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin k)
    (F : State d→ℝ) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hF : ContDiff ℝ (block choices factor).length F)
    (hfb : ∀ j,j≤(block choices factor).length → ∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (p : ℕ) (hp : 0<p) :
    let A := familyCovariance σ target center (referenceProfile P Λ u dir) lo hi
    let μ := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)
    Integrable (fun x => |VectorControlledRoot.value choices factor F mean g x|^(2*p)) μ ∧
      (∫ x,|VectorControlledRoot.value choices factor F mean g x|^(2*p) ∂μ)≤
        ControlledAssignedRoot.constant p choices factor*
          (VectorPhysicalRoot.scale choices factor lo hi A0 ν (P.lower/2) d)^(2*p) := by
  intro A μ
  by_cases hblock : block choices factor=[]
  · have hb (x : (Fin r→State n)×State n) : |VectorControlledRoot.value choices factor F mean g x|≤A0 := by
      simpa only [VectorControlledRoot.value,VectorJointRoot.value,hblock,GaussianVectorFractions.fractionDifferences,List.foldr_nil,
        norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,mul_one] using
        hfb 0 (Nat.zero_le _) (VectorRootClips.affineSum (projection g (mean+x.2))
          (fun _ : Fin r => projection g) (suppress (suppressed choices factor) x.1))
    have hpow (x : (Fin r→State n)×State n) := pow_le_pow_left₀ (abs_nonneg _) (hb x) (2*p)
    have hif : Integrable (fun x => |VectorControlledRoot.value choices factor F mean g x|^(2*p)) μ :=
      (integrable_const (A0^(2*p))).mono' (by
        have hf := VectorControlledRoot.value_measurable choices factor F hF.continuous.measurable mean g
        fun_prop) (ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)];exact hpow x))
    refine ⟨hif,?_⟩
    have hh := integral_mono hif (integrable_const (A0^(2*p))) hpow
    simpa [ControlledAssignedRoot.constant,VectorPhysicalRoot.scale,hblock] using hh
  · have hh := VectorPhysicalRoot.root_even_moment σ target center hσ hσ1 hages _
      (referenceProfile_measurable P Λ u dir)
      (fun z => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u dir z).1,
        (referenceProfile_bounds P Λ u dir z).2⟩) lo hi hlo hgap hstop B choices hnd factor
      (List.length_pos_iff.mpr hblock) g F hA0 hν hF hfb
      (fun y => projection g (mean+y)) (by fun_prop) p hp
    simpa only [VectorControlledRoot.value,ControlledAssignedRoot.constant,hblock,ite_false] using hh

end SHE.WindowAssignedFactors
