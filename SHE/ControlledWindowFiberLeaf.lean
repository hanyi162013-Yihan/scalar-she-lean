module

public import SHE.ControlledWindowOffsetLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledWindowFiberLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedGaussianFeatures StoppedFourier ProfileVariance
  GaussianCenteredLeafMoments
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n r : ℕ}

def scale (P : CanonicalCovariance.ProfileParameters) (mean ref age : ℝ) : ℝ :=
  P.holder*(|mean-ref|^P.exponent+(upperConstant*P.upper)^(P.exponent/2)*age^(P.exponent/4))

def constant (P : CanonicalCovariance.ProfileParameters) (p : ℕ) : ℝ :=
  (2:ℝ)^(2*p-1)*(1+leafMomentConstant p P.exponent)

/-- Conditional future rough-leaf moments at an arbitrary current mean.
The full baseline is unchanged; the mean discrepancy remains explicit. -/
theorem even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j k,j≠k → hi j≤lo k ∨ hi k≤lo j)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ j,σ j≤target j)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j)
    (i : Fin n) (hnative : σ i=target i) (ht : target i∈Ioc 0 P.horizon)
    (is : List (Fin r)) (mean : ℝ) (p : ℕ) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      σ target center q θ
    let ν := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)
    let ref := ControlledProfile.mean Λ u d (θ,(target i,center i))
    let F := fun x : (Fin r→State n)×State n =>
      P.coefficient (mean+((∑ j,suppress is x.1 j)+x.2) i)-
        ControlledProfile.profile P Λ u d (θ,(target i,center i))
    Integrable (fun x => |F x|^(2*p)) ν ∧
      (∫ x,|F x|^(2*p) ∂ν) ≤ constant P p*(scale P mean ref (target i))^(2*p) := by
  intro A B ν ref F
  let ρ : Measure Unit := Measure.dirac ()
  have hh := ControlledWindowOffsetLeaf.even_moment ρ P Λ u d θ lo hi hdisjoint σ target center hages
    hq hlo i hnative ht is (fun _ => mean) measurable_const p (integrable_const _)
  have hm : Measurable (fun x => |F x|^(2*p)) := by
    dsimp [F]
    simp_rw [SuppressedGaussianLaw.suppress_apply]
    exact (continuous_abs.measurable.comp ((P.measurable.comp (by fun_prop)).sub measurable_const)).pow_const _
  have hpres := measurePreserving_snd (μ:=ρ) (ν:=ν)
  have hiF : Integrable (fun x => |F x|^(2*p)) ν := by
    apply (hpres.integrable_comp hm.aestronglyMeasurable).mp
    convert! hh.1 using 1
  have he := hpres.hasLaw.integral_comp (f:=fun x => |F x|^(2*p)) hm.aestronglyMeasurable
  have hb : (∫ x,|F x|^(2*p) ∂ν) ≤ (2:ℝ)^(2*p-1)*
      (P.holder^(2*p)*|mean-ref|^(((2*p:ℕ):ℝ)*P.exponent)+leafMomentConstant p P.exponent*
        (P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4))^(2*p)) := by
    have h := hh.2
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
    convert! h using 1
    exact he.symm
  refine ⟨hiF,hb.trans ?_⟩
  have hnoise : 0≤(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4) :=
    mul_nonneg (rpow_nonneg (mul_nonneg upperConstant_pos.le P.upper_nonneg) _)
      (rpow_nonneg ht.1.le _)
  have hs0 : P.holder*|mean-ref|^P.exponent≤scale P mean ref (target i) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnoise) P.holder_nonneg
  have hs1 : P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4)≤
      scale P mean ref (target i) := by
    convert! mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (rpow_nonneg (abs_nonneg (mean-ref)) _))
      P.holder_nonneg using 1
    ring
  have hoff : P.holder^(2*p)*|mean-ref|^(((2*p:ℕ):ℝ)*P.exponent)=
      (P.holder*|mean-ref|^P.exponent)^(2*p) := by
    rw [mul_pow,←Real.rpow_mul_natCast (abs_nonneg (mean-ref))]
    congr 1
    congr 1
    ring
  rw [hoff]
  have h0 := pow_le_pow_left₀ (mul_nonneg P.holder_nonneg (rpow_nonneg (abs_nonneg (mean-ref)) _)) hs0 (2*p)
  have hn1 : 0≤P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4) :=
    mul_nonneg (mul_nonneg P.holder_nonneg
      (rpow_nonneg (mul_nonneg upperConstant_pos.le P.upper_nonneg) _)) (rpow_nonneg ht.1.le _)
  have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn1 hs1 (2*p))
    (leafMomentConstant_nonneg p P.exponent)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (show 0≤(2:ℝ)^(2*p-1) by positivity)
  unfold constant
  convert! hsum using 1
  ring

end SHE.ControlledWindowFiberLeaf
