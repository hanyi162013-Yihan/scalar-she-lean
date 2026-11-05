module

public import SHE.VaryingControlledGaussianFields
public import SHE.SignedInputMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PointwiseSignedGaussianWord
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance pointwiseSignedGaussianWord_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {n d r m : ℕ}
open FullResidualAssignedMoments

/-- Signed continuum covariance input is averaged BEFORE the native
probability space. All Gaussian data are deterministic at this step,
and the exact affine native-offset budget remains outside the input
mass. Thus this inequality may subsequently be evaluated at actual
past-dependent data without a fixed-law probability-space substitution. -/
theorem covariance_input_bound (νX : Measure X) [SFinite νX]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (row : X→State n) (hrow : Measurable row)
    (hB : (ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi)
      σ target center q θ).PosSemidef)
    (hrowRange : ∀ᵐ x ∂νX,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi)
        σ target center q θ)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (e : X→ℝ) (he : Measurable e)
    (hEnergy : Integrable (fun x=>|e x| *scoreVariance
      (ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi)
        σ target center q θ) (row x)) νX)
    (K : ℝ) (hK : 0≤K)
    (hgeom : |(∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
      VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
      ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)|≤K) :
    let B := ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi)
      σ target center q θ
    |(1/2:ℝ)*∫ x,e x*fibreAverage P Λ u d0 θ q σ target center lo hi mean true D (row x)
        g leaf choices F ∂νX|^(2*b)≤
      constant P r m choices b (currentBudget P Λ u d0 θ target center leaf mean b)*
        (((1/2:ℝ)*K)*∫ x,|e x| *scoreVariance B (row x) ∂νX)^(2*b) := by
  intro B
  let G : Unit×X→ℝ := fun z=>fibreAverage P Λ u d0 θ q σ target center lo hi mean true D (row z.2)
    g leaf choices F
  let V : X→ℝ := fun x=>scoreVariance B (row x)
  let C := constant P r m choices b (currentBudget P Λ u d0 θ target center leaf mean b)
  have hC : 0≤C := constant_nonneg P b choices
    (NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1))
  have hG : Measurable G := by
    have hh := VaryingControlledGaussianFields.fibreAverage_measurable P Λ θ q
      (fun _ : X=>u) (fun _ : X=>d0) measurable_const measurable_const σ target center lo hi
      (fun _ : X=>mean) measurable_const true (fun _=>D) (fun _=>measurable_const) row hrow
      g leaf choices F hFm
    exact hh.comp measurable_snd
  have hV : Measurable V := by
    convert! scoreVariance_measurable.comp (measurable_const.prodMk hrow) using 1
  have hV0 : ∀ᵐ x ∂νX,0≤V x := hrowRange.mono (fun _ hx=>scoreVariance_nonneg hB hx)
  have hpoint : ∀ᵐ x ∂νX,|G ((),x)|^(2*b)≤C*(V x*K)^(2*b) := by
    filter_upwards [hrowRange,hV0] with x hx hv
    have hh := pointwise_even_moment P Λ u d0 θ q hq σ target center hσ hσ1 hages lo hi hlo hlohi
      hstop hdisjoint mean true D hD (row x) hx g leaf hnative ht choices hnd chosen hchosen
      F hFm hA0 hν hf hfb b hb
    dsimp only at hh
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [←pow_abs_two_mul]
    have he : |((∏ j,scoreVariance
        (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
        scale true B (row x))*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
        ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)|=
        V x*|(∏ j,scoreVariance
        (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
        VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
        ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)| := by
      have hmul (s t w v0 : ℝ) (hv0 : 0≤v0) : |((s*v0)*t)*w|=v0*|(s*t)*w| := by
        rw [show ((s*v0)*t)*w=v0*((s*t)*w) by ring,abs_mul,abs_of_nonneg hv0]
      exact hmul _ _ _ (V x) hv
    rw [he]
    exact pow_le_pow_left₀ (mul_nonneg hv (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hgeom hv) _
  have hi : ∀ᵐ x ∂νX,Integrable (fun w : Unit=>|G (w,x)|^(2*b)) (Measure.dirac ()) :=
    ae_of_all _ (fun x=>by simpa only [G] using
      (integrable_const (|fibreAverage P Λ u d0 θ q σ target center lo hi mean true D (row x)
        g leaf choices F|^(2*b)) : Integrable (fun _ : Unit=>_) (Measure.dirac ())))
  have hbnd : ∀ᵐ x ∂νX,(∫ w : Unit,|G (w,x)|^(2*b) ∂Measure.dirac ())≤C*(V x*K)^(2*b) := by
    simpa only [integral_dirac] using hpoint
  have hh := SignedInputMoments.weighted_even_moment (Measure.dirac ()) νX G hG V e hV he
    hV0 hEnergy hK hC b hb hi hbnd
  have hp : |(1/2:ℝ)*∫ x,e x*G ((),x) ∂νX|^(2*b)=
      (1/2:ℝ)^(2*b)*|∫ x,e x*G ((),x) ∂νX|^(2*b) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow]
  rw [hp]
  have hf := mul_le_mul_of_nonneg_left (by simpa only [integral_dirac] using hh.2)
    (show 0≤(1/2:ℝ)^(2*b) by positivity)
  convert! hf using 1 <;> simp only [mul_pow] <;> ring

end SHE.PointwiseSignedGaussianWord

