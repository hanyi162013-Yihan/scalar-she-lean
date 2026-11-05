module

public import SHE.BoundedCompleteCovarianceInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.BoundedVaryingCovarianceInput
open Set MeasureTheory ProbabilityTheory StoppedFourier StoppedGaussianFeatures GaussianIncrement
  GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance MeasurableGaussianScores
open FullResidualAssignedMoments (currentBudget)
open scoped BigOperators
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n r m : ℕ}

/-- Genuine varying-past covariance input moments. The entire Gaussian
word is estimated before averaging its current offset budget against the
actual past input mass; no fixed-law outer moment or independence is used. -/
theorem input_moment (μ : Measure Ω) [IsFiniteMeasure μ] (νX : Measure X) [SFinite νX]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (c : Ω×Domain→ℝ) (hc : Measurable c) (hcb : ∀ ω z,P.lower≤c (ω,z) ∧ c (ω,z)≤P.upper)
    (η q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : Ω→State n) (hm : Measurable mean) (D : Fin r→State n)
    (hD : ∀ ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ (u ω) (d ω)) lo hi j)).range)
    (row : X→State n) (hrow : Measurable row)
    (hrowRange : ∀ ω,∀ᵐ x ∂νX,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (stoppedCovariance σ target center
        (BoundedWindowDecomposition.residual P Λ (u ω) (d ω) lo hi (fun z=>c (ω,z))) q)).range)
    (g : Fin 1→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (F : State 1→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ r F) (hfb : ∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (e : Ω×X→ℝ) (he : Measurable e)
    (hEnergy : ∀ ω,Integrable (fun x=>|e (ω,x)| *scoreVariance
      (stoppedCovariance σ target center
        (BoundedWindowDecomposition.residual P Λ (u ω) (d ω) lo hi (fun z=>c (ω,z))) q)
          (row x)) νX)
    (K Cbar : ℝ) (hK : 0≤K)
    (hgeom : ∀ ω,|∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ (u ω) (d ω)) lo hi j) (D j)|≤K) :
    let mass := fun ω=>∫ x,|e (ω,x)| *scoreVariance
      (stoppedCovariance σ target center
        (BoundedWindowDecomposition.residual P Λ (u ω) (d ω) lo hi (fun z=>c (ω,z))) q)
          (row x) ∂νX
    let budget := fun ω=>currentBudget P Λ (u ω) (d ω) η target center leaf (mean ω) b
    Integrable (fun ω=>(mass ω)^(2*b)*MixedPastWordMoments.momentConstant P r m b (budget ω)) μ →
    (∫ ω,(mass ω)^(2*b)*MixedPastWordMoments.momentConstant P r m b (budget ω) ∂μ)≤
      Cbar*(∫ ω,(mass ω)^(2*b) ∂μ) →
    let G := fun ω=>(1/2:ℝ)*∫ x,e (ω,x)*BoundedCompleteGaussianWord.value P Λ (u ω) (d ω)
      (fun z=>c (ω,z)) η q σ target center lo hi (mean ω) true D (row x) g leaf F ∂νX
    Integrable (fun ω=>|G ω|^(2*b)) μ ∧ (∫ ω,|G ω|^(2*b) ∂μ)≤
      Cbar*(K*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*
        (∫ ω,(mass ω)^(2*b) ∂μ) := by
  intro mass budget hweightedI hweighted G
  have hB (ω : Ω) : (stoppedCovariance σ target center
      (BoundedWindowDecomposition.residual P Λ (u ω) (d ω) lo hi (fun z=>c (ω,z))) q).PosSemidef :=
    StoppedCovarianceSplit.covariance_posSemidef σ target center hages q
      (BoundedWindowDecomposition.residual_measurable P Λ (u ω) (d ω) lo hi _
        (hc.comp (measurable_const.prodMk measurable_id)))
      (fun z=>⟨(half_pos P.lower_pos).le.trans
        (BoundedWindowDecomposition.residual_bounds P Λ (u ω) (d ω) lo hi hdisjoint _ (hcb ω) z).1,
        (BoundedWindowDecomposition.residual_bounds P Λ (u ω) (d ω) lo hi hdisjoint _ (hcb ω) z).2⟩)
  have hG : Measurable G := by
    let cs:=assignments (m:=m+1) (List.finRange r)
    have hinner : Measurable (fun z : Ω×X=>BoundedCompleteGaussianWord.value P Λ (u z.1) (d z.1)
        (fun w=>c (z.1,w)) η q σ target center lo hi (mean z.1) true D (row z.2) g leaf F) := by
      have heq : (fun z : Ω×X=>BoundedCompleteGaussianWord.value P Λ (u z.1) (d z.1)
          (fun w=>c (z.1,w)) η q σ target center lo hi (mean z.1) true D (row z.2) g leaf F)=
          (fun z=>(1/2:ℝ)^r*∑ j : Fin cs.length,BoundedResidualAssignedMoments.fibreAverage P Λ (u z.1) (d z.1) (fun w=>c (z.1,w)) η q
            σ target center lo hi (mean z.1) true D (row z.2) g leaf (cs.get j) F) :=
        funext (fun _=>congrArg (fun a:ℝ=>(1/2:ℝ)^r*a) (FiniteAssignmentMoments.map_sum_eq_fin cs _))
      rw [heq]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro j _
      exact BoundedResidualFields.fibreAverage_measurable P Λ η q
        (fun z : Ω×X=>u z.1) (fun z : Ω×X=>d z.1) (hu.comp measurable_fst) (hd.comp measurable_fst)
        (fun z : (Ω×X)×Domain=>c (z.1.1,z.2)) (hc.comp (measurable_fst.fst.prodMk measurable_snd))
        σ target center lo hi (fun z : Ω×X=>mean z.1) (hm.comp measurable_fst) true
        (fun _=>D) (fun _=>measurable_const) (fun z : Ω×X=>row z.2) (hrow.comp measurable_snd)
        g leaf (cs.get j) F hFm
    exact (((he.mul hinner).stronglyMeasurable.integral_prod_right').measurable).const_mul _
  have hp (ω : Ω) : |G ω|^(2*b)≤
      (K*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*((mass ω)^(2*b)*MixedPastWordMoments.momentConstant P r m b (budget ω)) := by
    have hh := BoundedCompleteCovarianceInput.bound νX P Λ (u ω) (d ω) (fun z=>c (ω,z))
      (hc.comp (measurable_const.prodMk measurable_id)) (hcb ω) η q hq σ target center hσ hσ1 hages
      lo hi hlo hlohi hstop hdisjoint (mean ω) D (hD ω) row hrow (hB ω) (hrowRange ω)
      g leaf hnative ht F hFm hA0 hν hf hfb b hb
      (fun x=>e (ω,x)) (he.comp (measurable_const.prodMk measurable_id)) (hEnergy ω) K hK (hgeom ω)
    convert! hh using 1 <;> simp only [mul_pow] <;> ring
  have hci : Integrable (fun ω=>(K*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*((mass ω)^(2*b)*MixedPastWordMoments.momentConstant P r m b (budget ω))) μ :=
    hweightedI.const_mul _
  have hgi : Integrable (fun ω=>|G ω|^(2*b)) μ := hci.mono'
    ((continuous_abs.measurable.comp hG).pow_const _).aestronglyMeasurable
    (ae_of_all _ (fun ω=>by simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hp ω))
  refine ⟨hgi,?_⟩
  have hbnd : (∫ ω,(K*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*((mass ω)^(2*b)*MixedPastWordMoments.momentConstant P r m b (budget ω)) ∂μ)≤
      (K*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>target (leaf j)) A0 ν/2)^(2*b)*(Cbar*(∫ ω,(mass ω)^(2*b) ∂μ)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hweighted ((even_two_mul b).pow_nonneg _)
  have hh := (integral_mono hgi hci hp).trans hbnd
  convert! hh using 1 <;> ring

end SHE.BoundedVaryingCovarianceInput
