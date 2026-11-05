module

public import SHE.NativeAssignedLeafMoments
public import SHE.DependentWordMoments
public import SHE.GaussianFractionMixedMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.NativeFirstScoreWordMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores
open scoped NNReal ENNReal BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

def word (a : ℝ→ℝ) (second : Fin r→Bool)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ) (mean : Ω→State n)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (z : Ω×((Fin r→State n)×State n)) : ℝ :=
  GaussianFractionMixedMoments.value second A D z.2.1*
    VectorControlledRoot.value choices 0 F (mean z.1) g z.2*
      ∏ j,ControlledAssignedLeaf.leaf choices j.succ a (mean z.1) (leaf j) (baseline j) z.2

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r×Fin (m+1))) (b : ℕ) (B0 : ℝ≥0) (κ M : ℝ) : ℝ :=
  productMomentConstant (b*(m+2))^r+ControlledAssignedRoot.constant (b*(m+2)) choices 0+
    ∑ j : Fin m,NativeAssignedLeafMoments.leafConstant P (b*(m+2)) B0 κ M choices j.succ

theorem word_measurable (a : ℝ→ℝ) (ha : Measurable a) (second : Fin r→Bool)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (D : Fin r→State n)
    (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ) (hF : Measurable F)
    (mean : Ω→State n) (hm : Measurable mean) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) : Measurable (word a second A D choices F mean g leaf baseline) :=
  ((GaussianFractionMixedMoments.measurable_value second A D).comp measurable_snd.fst).mul
    (ParametricAssignedMoments.root_measurable choices 0 F hF mean hm g) |>.mul
      (Finset.measurable_prod Finset.univ (fun j _ => ParametricAssignedMoments.leaf_measurable choices j.succ a ha mean hm (leaf j) (baseline j)))

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- All fixed moments of the actual native current-state Gaussian word.
The outer current state, every score, the root block and all rough
leaves remain jointly dependent. Every unassigned leaf has its full-age
gain from the SAME actual BDG input; assigned leaves and root blocks
retain their original old gaps and clips. -/
theorem joint_even_moment (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (σ target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hgap : ∀ i,(q:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    {θ : ℝ} (hθ : |θ|≤1) (second : Fin r→Bool) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target (nativeCenter centers) (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0) :
    let u := embed u₀
    let d0 := embed (v₀-u₀)
    let center := nativeCenter centers
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let mean := NativePairWindowLeaf.futureMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ
    let W := word P.coefficient second A D choices F mean g leaf
      (fun j => ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    Integrable (fun z => |W z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|W z|^(2*b) ∂μ.prod νG)≤constant P r m choices b B0 κ M*
        ((∏ j,scale (second j) (A j) (D j))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro u d0 center A B νG mean W
  have hM : 0≤M := hell.le.trans ((hb 0).1.trans (hb 0).2)
  have hm : Measurable mean := NativePairWindowLeaf.futureMean_measurable 𝓕 μ H Λ κ hκ ha hell hb
    I₀ I₁ u₀ v₀ S q target centers hgap θ
  let Score := fun z : Ω×((Fin r→State n)×State n) => GaussianFractionMixedMoments.value second A D z.2.1
  let Root := fun z : Ω×((Fin r→State n)×State n) => VectorControlledRoot.value choices 0 F (mean z.1) g z.2
  let Leaf := fun j : Fin m => fun z : Ω×((Fin r→State n)×State n) =>
    ControlledAssignedLeaf.leaf choices j.succ P.coefficient (mean z.1) (leaf j)
      (ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) z.2
  have hA (j : Fin r) : (A j).PosSemidef := covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d0)
    (fun p => ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d0 p).1,
      (referenceProfile_bounds P Λ u d0 p).2⟩) (lo j) (hi j)
  have hSm : Measurable Score := (GaussianFractionMixedMoments.measurable_value second A D).comp measurable_snd.fst
  have hRm : Measurable Root := ParametricAssignedMoments.root_measurable choices 0 F hFm mean hm g
  have hLm (j : Fin m) : Measurable (Leaf j) := ParametricAssignedMoments.leaf_measurable choices j.succ
    P.coefficient P.measurable mean hm (leaf j) _
  have hs0 := GaussianFractionMixedMoments.residual_even_moment second A hA D hD B (b*(m+2))
  have hs := UniformFiberMoments.even_moment μ νG Score hSm (b*(m+2))
    (productMomentConstant (b*(m+2))^r*(∏ j,scale (second j) (A j) (D j))^(2*(b*(m+2))))
    (fun _ => hs0.1) (fun _ => hs0.2)
  have hr := ParametricAssignedMoments.root_even_moment μ P Λ u d0 lo hi σ target center hσ hσ1 hages
    (fun j => q.2.trans (hlo j)) hlohi hstop B mean hm g choices hnd 0 F hFm hA0 hν hf hfb
    (b*(m+2)) (Nat.mul_pos hb0 (by omega))
  have hl (j : Fin m) := NativeAssignedLeafMoments.even_moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ P hΛ q hqH hq1 σ target centers hσ hσ1 hages hgap lo hi hlo hlohi hstop hdisjoint hθ
    (leaf j) (hnative j) (ht j) choices hnd j.succ (chosen j) (hchosen j) (b*(m+2)) B0 hBDG
  have hLC (j : Fin m) : 0≤NativeAssignedLeafMoments.leafConstant P (b*(m+2)) B0 κ M choices j.succ := by
    unfold NativeAssignedLeafMoments.leafConstant NativeAssignedLeafMoments.emptyConstant
    split_ifs
    · have hc : 0≤NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M := by
        dsimp [NativeHybridMoments.momentConstant]
        exact mul_nonneg B0.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)
      exact mul_nonneg (by positivity) (add_nonneg (rpow_nonneg hc _)
        (mul_nonneg (GaussianCenteredLeafMoments.leafMomentConstant_nonneg _ _)
          (pow_nonneg (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le P.upper_nonneg) _) _)))
    · exact GaussianAudit.gaussianAbsMoment_nonneg _
  have hLS (j : Fin m) : 0≤NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j) := by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs
    · exact mul_nonneg P.holder_nonneg (rpow_nonneg (ht j).1.le _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
        (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
        (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
  simp only [←Nat.mul_assoc] at hs hr hl
  exact DependentWordMoments.word_even_moment (μ.prod νG) Score Root Leaf hSm hRm hLm
    (∏ j,scale (second j) (A j) (D j))
    (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d)
    (fun j => NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))
    (Finset.prod_nonneg (fun j _ => scale_nonneg (hA j) (hD j) _))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j => (hlohi j).le) hA0 hν d) hLS
    _ _ _ (pow_nonneg (productMomentConstant_nonneg _) _) (ControlledAssignedRoot.constant_nonneg _ _ _) hLC
    b hs.1 hr.1 (fun j => (hl j).1) hs.2 hr.2 (fun j => (hl j).2)

end SHE.NativeFirstScoreWordMoments
