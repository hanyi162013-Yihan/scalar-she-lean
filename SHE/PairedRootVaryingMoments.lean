module

public import SHE.NoFreshOffsetCalculus
public import SHE.PairedRootWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.PairedRootVaryingMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open NoFreshAssignedMoments
open scoped BigOperators
local instance pairedRootVaryingMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

/-- The literal current-root normalized old/future Gaussian average.
The actual current increment is removed BEFORE any probability integral. -/
def fibreAverage (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d0:CircleL2) (θ q:ℝ)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (newMean oldMean:State n) (leafMean:Fin m→State n) (η:Fin m→ℝ) (D:Fin r→State n)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ) (ν χ:ℝ) : ℝ :=
  let A:=familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
  let B:=ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
  let source:=(min 1 (ν*‖GaussianCoordinates.projection g (newMean-oldMean)‖))^χ
  ∫x,(∏j,secondScore (A j) (D j) (x.1 j))*
    NormalizedScalarMoment.value
      (VectorControlledRoot.value choices 0 F newMean g x-VectorControlledRoot.value choices 0 F oldMean g x) source*
      ∏j,ControlledAssignedLeaf.leaf choices j.succ P.coefficient (leafMean j) (leaf j)
        (ControlledProfile.profile P Λ u d0 (η j,(target (leaf j),center (leaf j)))) x
    ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)

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
    (newMean oldMean : Ω→State n) (leafMean : Fin m→Ω→State n) (η:Fin m→ℝ) (D : Ω→Fin r→State n)
    (hD : ∀ ω j,D ω j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi j)).range)
    (g : Fin 1→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State 1→ℝ) (hFm : Measurable F) {A0 ν χ : ℝ} (hA0 : 0≤A0) (hν : 0≤ν) (hχ:0≤χ) (hχ1:χ≤1)
    (hf : ContDiff ℝ ((block choices 0).length+1) F)
    (hfb : ∀ j,j≤(block choices 0).length+1→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (C0 : ℝ)
    (hoffset : ∀ j,Integrable (fun ω=>|leafMean j ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
      (η j,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|leafMean j ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
        (η j,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
      C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)*μ.real Set.univ)
    (hG : Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi (newMean ω) (oldMean ω) (fun j=>leafMean j ω) η (D ω) g leaf choices F ν χ))
    (K : ℝ) (hK : 0≤K)
    (hgeom : ∀ᵐ ω ∂μ,
      let A := familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi
      let B := ControlledFixedReserve.covariance P Λ (u ω) (d0 ω) (fixedProfile P Λ (u ω) (d0 ω) lo hi) σ target center q θ
      |(∏ j,scoreVariance (A j) (D ω j))*
        (2*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1)*
        ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)|≤K) :
    let G := fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi (newMean ω) (oldMean ω) (fun j=>leafMean j ω) η (D ω) g leaf choices F ν χ
    Integrable (fun ω=>|G ω|^(2*b)) μ ∧
      (∫ ω,|G ω|^(2*b) ∂μ)≤constant P r m choices b ((m:ℝ)*C0)*K^(2*b)*μ.real Set.univ := by
  intro G
  let offset:=fun ω j=>leafMean j ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
    (η j,(target (leaf j),center (leaf j)))
  let budget:=fun ω=>NormalizedLeafOffsets.budget (fun j=>target (leaf j)) (offset ω)
    (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ((b*(m+2):ℕ)*P.exponent/2)
  have hbudget (ω : Ω) : 0≤budget ω := NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1)
  have hbudgetI : Integrable budget μ := NormalizedLeafOffsets.budget_integrable μ _ _ _ _ (fun j=>(hoffset j).1)
  have hb : (∫ ω,budget ω ∂μ)≤(m:ℝ)*C0*μ.real Set.univ :=
    NormalizedLeafOffsets.integral_budget_le μ _ (fun j=>(ht j).1) _ _ _ C0
      (fun j=>(hoffset j).1) (fun j=>(hoffset j).2)
  have hci := constant_budget_integrable μ P b choices budget hbudgetI
  have hcb := integral_constant_budget_le μ P b choices budget hbudgetI ((m:ℝ)*C0) hb
  have hbound : ∀ᵐ ω ∂μ,|G ω|^(2*b)≤constant P r m choices b (budget ω)*K^(2*b) := by
    filter_upwards [hgeom] with ω hω
    have hh := PairedRootWordMoments.even_moment P Λ (u ω) (d0 ω) θ η σ target center hσ hσ1 hages
      q hq lo hi hlo hlohi hstop hdisjoint (D ω) (hD ω)
      (newMean ω) (oldMean ω) (fun j=>leafMean j ω) g leaf hnative ht choices hnd chosen hchosen F hFm
      hA0 hν hχ hχ1 (hbudget ω) hf hfb b hb0
      (fun j=>by
        have ho:=NormalizedLeafOffsets.offset_le_budget (fun j=>target (leaf j)) (offset ω)
          (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ((b*(m+2):ℕ)*P.exponent/2) (fun j=>(ht j).1) j
        convert! ho using 1)
    dsimp only at hh hω
    have hbpoint : |G ω|^(2*b)≤constant P r m choices b (budget ω)*
      ((∏j,scoreVariance (familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi j) (D ω j))*
        (2*VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1)*
        ∏j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
      convert! hh.2.2 using 1
    apply hbpoint.trans
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

end SHE.PairedRootVaryingMoments
