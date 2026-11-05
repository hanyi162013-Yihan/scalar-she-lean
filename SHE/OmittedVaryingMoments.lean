module

public import SHE.OmittedOffsetCalculus
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.OmittedAssignedMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance omittedVaryingMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n d r m : ℕ}

/-- Literal omitted-leaf fibre integral, under the SAME physical old
fractions and full residual as the original word. -/
def fibreAverage (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ q : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (mean : State n) (D : Fin r→State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (F : State d→ℝ) : ℝ :=
  let A:=familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
  let B:=ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
  ∫ x,word A D choices j0 P.coefficient F (fun _ : Unit=>mean) g leaf
      (fun j=>ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) ((),x)
    ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A j))).prod (multivariateGaussian (0 : State n) B)

/-- Pointwise Gaussian omitted-word estimate at arbitrary current mean.
The exact offset budget remains explicit before any random-past average. -/
theorem pointwise_even_moment
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup) (j0 : Fin m)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) :
    |fibreAverage P Λ u d0 θ q σ target center lo hi mean D g leaf choices j0 F|^(2*b)≤
      constant P r m choices j0 b
        (FullResidualAssignedMoments.currentBudget P Λ u d0 θ target center leaf mean b)*
        ((∏ j,scoreVariance
            (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j∈Finset.univ.erase j0,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi
            (target (leaf j)) (chosen j))^(2*b) := by
  let C0:=FullResidualAssignedMoments.currentBudget P Λ u d0 θ target center leaf mean b
  have hC0 : 0≤C0:=NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1)
  have hoffset (j : Fin m) (_hj : j≠j0) :
      Integrable (fun _ : Unit=>|mean (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) (Measure.dirac ()) ∧
      (∫ _ : Unit,|mean (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂Measure.dirac ())≤C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2) := by
    refine ⟨integrable_const _,?_⟩
    rw [integral_const,probReal_univ,one_smul]
    exact NormalizedLeafOffsets.offset_le_budget (fun j=>target (leaf j))
      (fun j=>mean (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j))))
      (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ((b*(m+2):ℕ)*P.exponent/2) (fun j=>(ht j).1) j
  have hh:=averaged_even_moment (Measure.dirac ()) P Λ u d0 θ q hq σ target center hσ hσ1 hages
    lo hi hlo hlohi hstop hdisjoint (fun _ : Unit=>mean) measurable_const D hD g leaf hnative ht
    choices hnd j0 chosen hchosen F hFm hA0 hν hf hfb b hb C0 hC0 hoffset
  dsimp only at hh
  simpa only [fibreAverage,C0,integral_dirac] using hh.2

attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

theorem varying_average_measurable
    (A : Ω→Fin r→MeasurableGeneralizedInverse.Mat n) (hA : ∀ j,Measurable (fun ω=>A ω j))
    (D : Ω→Fin r→State n) (hD : ∀ j,Measurable (fun ω=>D ω j))
    (B : Ω→MeasurableGeneralizedInverse.Mat n) (hB : Measurable B)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (a : ℝ→ℝ) (ha : Measurable a)
    (F : State d→ℝ) (hF : Measurable F) (mean : Ω→State n) (hm : Measurable mean)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Ω→Fin m→ℝ)
    (hbase : ∀ j,Measurable (fun ω=>baseline ω j)) :
    Measurable (fun ω=>∫ x,word (A ω) (D ω) choices j0 a F (fun _ : Unit=>mean ω) g leaf
      (baseline ω) ((),x) ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A ω j))).prod
        (multivariateGaussian (0 : State n) (B ω))) := by
  have hold (j : Fin r) : Measurable (fun z : Ω×((Fin r→State n)×State n)=>
      secondScore (A z.1 j) (D z.1 j) (z.2.1 j)) := by
    have hy : Measurable (fun z : Ω×((Fin r→State n)×State n)=>z.2.1 j) :=
      (measurable_pi_apply j).comp measurable_snd.fst
    have hp : Measurable (fun z : Ω×((Fin r→State n)×State n)=>((A z.1 j,D z.1 j),z.2.1 j)) :=
      (((hA j).comp measurable_fst).prodMk ((hD j).comp measurable_fst)).prodMk hy
    convert! (secondScore_measurable (n:=n)).comp hp using 1
  have hroot:=ParametricAssignedMoments.root_measurable choices 0 F hF mean hm g
  have hleaves:=Finset.measurable_prod (Finset.univ.erase j0)
    (fun j _=>VaryingAssignedFields.leaf_measurable choices j.succ a ha mean hm (leaf j)
      (fun ω=>baseline ω j) (hbase j))
  have hword : Measurable (fun z : Ω×((Fin r→State n)×State n)=>word (A z.1) (D z.1)
      choices j0 a F (fun _ : Unit=>mean z.1) g leaf (baseline z.1) ((),z.2)) := by
    convert! (((Finset.measurable_prod Finset.univ (fun j _=>hold j)).mul hroot).mul hleaves) using 1
  let κold:=FiniteKernelProduct.kernel r (fun j=>GaussianScoreKernel.gaussianKernel (fun ω=>A ω j) (hA j))
  let κ:=κold.prod (GaussianScoreKernel.gaussianKernel B hB)
  have hh:=(hword.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  convert! hh using 1
  funext ω
  rw [show κ ω=(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A ω j))).prod
      (multivariateGaussian (0 : State n) (B ω)) by
    dsimp only [κ]
    rw [ProbabilityTheory.Kernel.prod_apply,FiniteKernelProduct.kernel_apply]
    rfl]

/-- Genuine joint Borel dependence of the omitted integral through
arbitrary random controlled references, including changing covariance rank. -/
theorem fibreAverage_measurable (P : CanonicalCovariance.ProfileParameters) (Λ θ q : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (mean : Ω→State n) (hm : Measurable mean) (D : Ω→Fin r→State n)
    (hD : ∀ j,Measurable (fun ω=>D ω j)) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (choices : List (Fin r×Fin (m+1))) (j0 : Fin m) (F : State d→ℝ) (hF : Measurable F) :
    Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi (mean ω)
      (D ω) g leaf choices j0 F) := by
  have hbase (j : Fin m) : Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (θ,(target (leaf j),center (leaf j)))) := by
    convert! (VaryingControlledGaussianFields.profile_measurable P Λ θ u d0 hu hd).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
  exact varying_average_measurable _
    (fun j=>VaryingControlledGaussianFields.old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j)
    D hD _ (VaryingControlledGaussianFields.residual_covariance_measurable P Λ θ q u d0 hu hd σ target center lo hi)
    choices j0 P.coefficient P.measurable F hF mean hm g leaf _ hbase

end SHE.OmittedAssignedMoments

