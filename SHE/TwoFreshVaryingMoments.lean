module

public import SHE.TwoFreshPointwiseMoments
public import SHE.TwoFreshOffsetWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.TwoFreshFullResidualMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance twoFreshVaryingMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

/-- The literal fibre Gaussian average, including every original old
covariance and the full residual covariance. -/
def fibreAverage (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ q : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (mean : State n) (second : Bool) (D : Fin r→State n) (E V : State n)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ) : ℝ :=
  let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
  let R := NativeFirstScoreReserve.covariance P σ target center q
  let C := ControlledFixedReserve.covariance P Λ u d0
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ
  ∫ x,word second A D R C E V choices P.coefficient F (fun _ : Unit=>mean) g leaf
      (fun j=>ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) ((),x)
    ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod ((multivariateGaussian (0 : State n) R).prod (multivariateGaussian (0 : State n) C))

/-- TRUE varying-data Gaussian moments. The original initial state,
controlled reference, all old laws, residual law, score directions and
current mean may vary arbitrarily together with omega. The proof is
pointwise Gaussian followed by the affine actual-offset budget; it does
not invoke a fixed-covariance outer moment theorem on random past data. -/
theorem varying_even_moment (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : Ω→CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : Ω→State n) (second : Bool) (D : Ω→Fin r→State n)
    (hD : ∀ ω j,D ω j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi j)).range)
    (E V : Ω→State n) (hE : ∀ ω,E ω∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (hV : ∀ ω,V ω∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ (u ω) (d0 ω)
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u ω) (d0 ω) lo hi)) σ target center q θ)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (C0 : ℝ)
    (hoffset : ∀ j,Integrable (fun ω=>|mean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
      (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
      C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)*μ.real Set.univ)
    (hG : Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi (mean ω) second (D ω) (E ω) (V ω) g leaf choices F))
    (K : ℝ) (hK : 0≤K)
    (hgeom : ∀ᵐ ω ∂μ,
      let A := familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi
      let R := NativeFirstScoreReserve.covariance P σ target center q
      let C := ControlledFixedReserve.covariance P Λ (u ω) (d0 ω)
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u ω) (d0 ω) lo hi)) σ target center q θ
      |((∏ j,scoreVariance (A j) (D ω j))*Real.sqrt (scoreVariance R (E ω))*scale second C (V ω))*
        VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
        ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)|≤K) :
    let G := fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi (mean ω) second (D ω) (E ω) (V ω) g leaf choices F
    Integrable (fun ω=>|G ω|^(2*b)) μ ∧
      (∫ ω,|G ω|^(2*b) ∂μ)≤constant P r m choices b ((m:ℝ)*C0)*K^(2*b)*μ.real Set.univ := by
  intro G
  let budget := fun ω=>currentBudget P Λ (u ω) (d0 ω) θ target center leaf (mean ω) b
  have hbudget (ω : Ω) : 0≤budget ω := NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1)
  have hbudgetI : Integrable budget μ := NormalizedLeafOffsets.budget_integrable μ _ _ _ _ (fun j=>(hoffset j).1)
  have hb : (∫ ω,budget ω ∂μ)≤(m:ℝ)*C0*μ.real Set.univ :=
    NormalizedLeafOffsets.integral_budget_le μ _ (fun j=>(ht j).1) _ _ _ C0
      (fun j=>(hoffset j).1) (fun j=>(hoffset j).2)
  have hci := constant_budget_integrable μ P b choices budget hbudgetI
  have hcb := integral_constant_budget_le μ P b choices budget hbudgetI ((m:ℝ)*C0) hb
  have hbound : ∀ᵐ ω ∂μ,|G ω|^(2*b)≤constant P r m choices b (budget ω)*K^(2*b) := by
    filter_upwards [hgeom] with ω hω
    have hh := pointwise_even_moment P Λ (u ω) (d0 ω) θ q hq σ target center hσ hσ1 hages
      lo hi hlo hlohi hstop hdisjoint (mean ω) second (D ω) (hD ω) (E ω) (V ω) (hE ω) (hV ω)
      g leaf hnative ht choices hnd chosen hchosen F hFm hA0 hν hf hfb b hb0
    dsimp only at hh hω
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (constant_nonneg P b choices (hbudget ω))
    rw [←pow_abs_two_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) hω _
  have hgi : Integrable (fun ω=>|G ω|^(2*b)) μ := (hci.mul_const (K^(2*b))).mono'
    ((continuous_abs.measurable.comp hG).pow_const _).aestronglyMeasurable
    (by filter_upwards [hbound] with ω hω; simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hω)
  refine ⟨hgi,?_⟩
  have hfinal : (∫ ω,|G ω|^(2*b) ∂μ)≤
      (constant P r m choices b ((m:ℝ)*C0)*μ.real Set.univ)*K^(2*b) := by
    apply (integral_mono_ae hgi (hci.mul_const (K^(2*b))) hbound).trans
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hcb (pow_nonneg hK _)
  convert! hfinal using 1 <;> ring

end SHE.TwoFreshFullResidualMoments
