module

public import SHE.ControlledWindowDecomposition
public import SHE.SuppressedShiftedReference
public import SHE.GaussianTwoProfileLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.TwoProfileWindowLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianCenteredLeafMoments ControlledOldIntervals OldIntervalCovariance
  StoppedGaussianFeatures StoppedFourier ProfileVariance GaussianAudit
open scoped BigOperators NNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n r : ℕ}

/-- The future law belongs to theta, while the leaf retains its OWN
eta endpoint baseline. Both variances obey the physical age cap; no
ordering or equality between the two endpoint profiles is assumed. -/
theorem even_moment {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ η : ℝ) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j k,j≠k → hi j≤lo k ∨ hi k≤lo j)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ j,σ j≤target j)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j)
    (i : Fin n) (hnative : σ i=target i) (ht : target i∈Ioc 0 P.horizon)
    (is : List (Fin r)) (m : Ω×((Fin r→State n)×State n)→ℝ) (hm : Measurable m) (p : ℕ) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      σ target center q θ
    let ν := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let ref := ControlledProfile.mean Λ u d (η,(target i,center i))
    Integrable (fun z => |m z-ref|^(((2*p:ℕ):ℝ)*P.exponent)) (ρ.prod ν) →
    Integrable (fun z => |P.coefficient (m z+((∑ j,suppress is z.2.1 j)+z.2.2) i)-
      ControlledProfile.profile P Λ u d (η,(target i,center i))|^(2*p)) (ρ.prod ν) ∧
      (∫ z,|P.coefficient (m z+((∑ j,suppress is z.2.1 j)+z.2.2) i)-
        ControlledProfile.profile P Λ u d (η,(target i,center i))|^(2*p) ∂ρ.prod ν) ≤
      (2 : ℝ)^(2*p-1)*(P.holder^(2*p)*
        (∫ z,|m z-ref|^(((2*p:ℕ):ℝ)*P.exponent) ∂ρ.prod ν)+
        leafMomentConstant p P.exponent*
          (P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4))^(2*p)) := by
  intro A B ν ref hiOffset
  have hcref (z : ControlledProfile.Domain) : 0≤referenceProfile P Λ u d z ∧
      referenceProfile P Λ u d z≤P.lower/2 :=
    ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d z).1,
      (referenceProfile_bounds P Λ u d z).2⟩
  have hA (j : Fin r) : (A j).PosSemidef := OldIntervalCovariance.covariance_posSemidef
    σ target center hages _ (referenceProfile_measurable P Λ u d) hcref (lo j) (hi j)
  have hc : Measurable (fun z => ControlledProfile.profile P Λ u d (θ,z)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hcb (z : ControlledProfile.Domain) : 0≤ControlledProfile.profile P Λ u d (θ,z) ∧
      ControlledProfile.profile P Λ u d (θ,z)≤P.upper :=
    ⟨P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (θ,z)).1,
      (ControlledProfile.profile_bounds P Λ u d (θ,z)).2⟩
  have hB : B.PosSemidef := by
    apply StoppedCovarianceSplit.covariance_posSemidef σ target center hages q
      (hc.sub (fixedProfile_measurable P Λ u d lo hi))
    intro z
    exact ⟨(half_pos P.lower_pos).le.trans (residual_bounds P Λ u d lo hi hdisjoint θ z).1,
      (residual_bounds P Λ u d lo hi hdisjoint θ z).2⟩
  let C := stoppedCovariance σ target center (fun z => ControlledProfile.profile P Λ u d (θ,z)) 0
  let E := stoppedCovariance σ target center (fun z => ControlledProfile.profile P Λ u d (η,z)) 0
  have hec : Measurable (fun z => ControlledProfile.profile P Λ u d (η,z)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have heb (z : ControlledProfile.Domain) : 0≤ControlledProfile.profile P Λ u d (η,z) ∧
      ControlledProfile.profile P Λ u d (η,z)≤P.upper :=
    ⟨P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (η,z)).1,
      (ControlledProfile.profile_bounds P Λ u d (η,z)).2⟩
  have hC : C.PosSemidef := StoppedCovarianceSplit.covariance_posSemidef σ target center hages 0 hc hcb
  have hE : E.PosSemidef := StoppedCovarianceSplit.covariance_posSemidef σ target center hages 0 hec heb
  have hdom : SuppressedGaussianLaw.covariance is A B i i≤C i i :=
    ControlledWindowDecomposition.suppressed_diagonal_le P Λ u d θ lo hi hdisjoint
      σ target center hages hq hlo is i
  have hdiag : C i i=varianceMap (fun z => ControlledProfile.profile P Λ u d (θ,z)) (target i) (center i) :=
    GaussianProfileBaseline.coordinate_covariance_eq_native σ target center _ hc P.upper hcb
      i hnative ht.1 (ht.2.trans P.horizon_le_one)
  have hediag : E i i=varianceMap (fun z => ControlledProfile.profile P Λ u d (η,z)) (target i) (center i) :=
    GaussianProfileBaseline.coordinate_covariance_eq_native σ target center _ hec P.upper heb
      i hnative ht.1 (ht.2.trans P.horizon_le_one)
  let cap : ℝ := upperConstant*P.upper*(target i)^(1/2 : ℝ)
  have hcap : 0≤cap := mul_nonneg (mul_nonneg upperConstant_pos.le P.upper_nonneg) (rpow_nonneg ht.1.le _)
  have hcCap : C i i≤cap := by
    rw [hdiag]
    exact (varianceMap_elliptic hc ht.1 (ht.2.trans P.horizon_le_one) (by norm_num : 0≤(0:ℝ))
      P.upper_nonneg (fun s _ y => (hcb (s,y)).1) (fun s _ y => (hcb (s,y)).2) (center i)).2
  have heCap : E i i≤cap := by
    rw [hediag]
    exact (varianceMap_elliptic hec ht.1 (ht.2.trans P.horizon_le_one) (by norm_num : 0≤(0:ℝ))
      P.upper_nonneg (fun s _ y => (heb (s,y)).1) (fun s _ y => (heb (s,y)).2) (center i)).2
  have hvCap : (SuppressedGaussianLaw.covariance is A B i i).toNNReal≤cap.toNNReal :=
    Real.toNNReal_le_toNNReal (hdom.trans hcCap)
  have heCap' : (E i i).toNNReal≤cap.toNNReal := Real.toNNReal_le_toNNReal heCap
  have hbase : GaussianProfile.gaussianAverage P.coefficient ref (E i i)=
      ControlledProfile.profile P Λ u d (η,(target i,center i)) := by
    rw [hediag]
    exact (ControlledProfile.profile_fixed P Λ u d η ht (center i)).symm
  have hbound (z : ℝ) : |P.coefficient z|≤P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  have hl := (SuppressedGaussianLaw.coordinate_hasLaw is A hA B hB i).fun_comp
    ((measurePreserving_snd (μ:=ρ) (ν:=ν)).hasLaw)
  have hXm : Measurable (fun z : Ω×((Fin r→State n)×State n) =>
      ((∑ j,suppress is z.2.1 j)+z.2.2) i) := by
    simp_rw [SuppressedGaussianLaw.suppress_apply]
    fun_prop
  have hh := GaussianTwoProfileLeaf.shifted_even_moment (ρ.prod ν) _ m hXm hm hl hvCap heCap'
    P.coefficient P.measurable P.upper P.holder P.exponent hbound P.holder_nonneg
    P.exponent_pos.le P.holder_bound ref p hiOffset
  simp only [Real.coe_toNNReal _ hE.diag_nonneg,hbase,Real.coe_toNNReal _ hcap] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp := PhysicalOldBlockMoments.physical_variance_power hcap P.upper_nonneg
    ht.1 P.exponent_pos.le (le_refl cap)
  have hs : P.holder*cap^(P.exponent/2)≤
      P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4) := by
    convert! mul_le_mul_of_nonneg_left hp P.holder_nonneg using 1
    ring
  have hh' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (mul_nonneg P.holder_nonneg (rpow_nonneg hcap _)) hs (2*p))
      (leafMomentConstant_nonneg p P.exponent)
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hh') (by positivity)

end SHE.TwoProfileWindowLeaf
