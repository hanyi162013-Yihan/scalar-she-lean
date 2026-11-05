module

public import SHE.NoFreshOffsetCalculus
public import SHE.PairedOffsetCalculus
public import SHE.PairedOffsetBudgets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.PairedRoughVaryingMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open NoFreshAssignedMoments
open scoped BigOperators
local instance pairedRoughVaryingMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

def leafScale (P:CanonicalCovariance.ProfileParameters)
    (choices:List (Fin r×Fin (m+1))) (j0:Fin m) (χ:ℝ) (lo hi:Fin r→ℝ) (target:Fin n→ℝ)
    (leaf:Fin m→Fin n) (chosen:∀j:Fin m,block choices j.succ≠[]→Fin r) (j:Fin m) : ℝ :=
  if j=j0 then PairedRoughWordMoments.pairScale P choices j0.succ χ lo hi (target (leaf j0)) (chosen j0)
  else NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j)

/-- The literal whole paired-rough Gaussian average, with own endpoint
baselines and a current-source-normalized pair. All other factors retain
the original finite-product telescope endpoint choice. -/
def fibreAverage (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d0:CircleL2)
    (θ ηOld ηNew q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (newMean oldMean rootMean:State n) (choose:Fin m→Bool) (D:Fin r→State n)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (choices:List (Fin r×Fin (m+1))) (j0:Fin m) (F:State 1→ℝ) (χ:ℝ) : ℝ :=
  let A:=familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
  let B:=ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
  let Pair:=PairedRoughWordMoments.value P choices j0.succ χ newMean oldMean (leaf j0)
    (ControlledProfile.profile P Λ u d0 (ηNew,(target (leaf j0),center (leaf j0))))
    (ControlledProfile.profile P Λ u d0 (ηOld,(target (leaf j0),center (leaf j0))))
  ∫x,(∏j,secondScore (A j) (D j) (x.1 j))*VectorControlledRoot.value choices 0 F rootMean g x*
    ∏j,if j=j0 then Pair x else ControlledAssignedLeaf.leaf choices j.succ P.coefficient
      (if choose j then newMean else oldMean) (leaf j)
      (ControlledProfile.profile P Λ u d0 ((if choose j then ηNew else ηOld),(target (leaf j),center (leaf j)))) x
    ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)

/-- TRUE varying-past paired-rough moments: every covariance and current
mean may depend on the same original sample. Only genuine conditional
endpoint offset packets are integrated; no random Gaussian-law
substitution and no multiplication of separate second moments occurs. -/
theorem varying_even_moment (μ:Measure Ω) [IsFiniteMeasure μ]
    (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d0:Ω→CircleL2) (θ ηOld ηNew:ℝ)
    (q:ℝ) (hq:0≤q) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i) (hσ1:∀i,σ i≤1) (hages:∀i,σ i≤target i)
    (lo hi:Fin r→ℝ) (hlo:∀j,q≤lo j) (hlohi:∀j,lo j<hi j)
    (hstop:∀j i,σ i≤lo j ∨ hi j≤σ i) (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (newMean oldMean rootMean:Ω→State n) (choose:Fin m→Bool) (D:Ω→Fin r→State n)
    (hD:∀ω j,D ω j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi j)).range)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n)
    (hnative:∀j,σ (leaf j)=target (leaf j)) (ht:∀j,target (leaf j)∈Ioc 0 P.horizon)
    (choices:List (Fin r×Fin (m+1))) (hnd:(choices.map Prod.fst).Nodup)
    (chosen:∀j:Fin m,block choices j.succ≠[]→Fin r) (hchosen:∀j h,chosen j h∈block choices j.succ)
    (j0:Fin m) (F:State 1→ℝ) (hFm:Measurable F) {A0 ν χ:ℝ}
    (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hf:ContDiff ℝ (block choices 0).length F)
    (hfb:∀j,j≤(block choices 0).length→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b:ℕ) (hb0:0<b) (C0:ℝ)
    (hOld:∀j,Integrable (fun ω=>|oldMean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
      (ηOld,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ω,|oldMean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
        (ηOld,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
        C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)*μ.real univ)
    (hNew:∀j,Integrable (fun ω=>|newMean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
      (ηNew,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ω,|newMean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
        (ηNew,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
        C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)*μ.real univ)
    (hG:Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ ηOld ηNew q σ target center lo hi
      (newMean ω) (oldMean ω) (rootMean ω) choose (D ω) g leaf choices j0 F χ))
    (K:ℝ) (hK:0≤K)
    (hgeom:∀ᵐ ω ∂μ, |(∏j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi j) (D ω j))*
      VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1*
      ∏j,leafScale P choices j0 χ lo hi target leaf chosen j|≤K) :
    let G:=fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ ηOld ηNew q σ target center lo hi
      (newMean ω) (oldMean ω) (rootMean ω) choose (D ω) g leaf choices j0 F χ
    Integrable (fun ω=>|G ω|^(2*b)) μ ∧
      (∫ω,|G ω|^(2*b) ∂μ)≤PairedRoughWordMoments.constant P choices j0 χ b (2*(m:ℝ)*C0)*K^(2*b)*μ.real univ := by
  intro G
  let age:=fun j=>target (leaf j)
  let oldOffset:=fun ω j=>oldMean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
    (ηOld,(target (leaf j),center (leaf j)))
  let newOffset:=fun ω j=>newMean ω (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
    (ηNew,(target (leaf j),center (leaf j)))
  let power:=(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)
  let degree:=((b*(m+2):ℕ)*P.exponent/2)
  let Bo:=fun ω=>NormalizedLeafOffsets.budget age (oldOffset ω) power degree
  let Bn:=fun ω=>NormalizedLeafOffsets.budget age (newOffset ω) power degree
  let budget:=fun ω=>Bo ω+Bn ω
  have ha:∀j,0<age j:=fun j=>(ht j).1
  have hBo:∀ω,0≤Bo ω:=fun ω=>NormalizedLeafOffsets.budget_nonneg age (oldOffset ω) power degree ha
  have hBn:∀ω,0≤Bn ω:=fun ω=>NormalizedLeafOffsets.budget_nonneg age (newOffset ω) power degree ha
  have hbudget:∀ω,0≤budget ω:=fun ω=>add_nonneg (hBo ω) (hBn ω)
  have hoi:Integrable Bo μ:=NormalizedLeafOffsets.budget_integrable μ age oldOffset power degree (fun j=>(hOld j).1)
  have hni:Integrable Bn μ:=NormalizedLeafOffsets.budget_integrable μ age newOffset power degree (fun j=>(hNew j).1)
  have hbi:Integrable budget μ:=hoi.add hni
  have hob:=NormalizedLeafOffsets.integral_budget_le μ age ha oldOffset power degree C0 (fun j=>(hOld j).1) (fun j=>(hOld j).2)
  have hnb:=NormalizedLeafOffsets.integral_budget_le μ age ha newOffset power degree C0 (fun j=>(hNew j).1) (fun j=>(hNew j).2)
  have hbb:(∫ω,budget ω ∂μ)≤(2*(m:ℝ)*C0)*μ.real univ := by
    change (∫ω,Bo ω+Bn ω ∂μ)≤_
    rw [integral_add hoi hni]
    linarith
  have hc:=PairedRoughWordMoments.weighted_constant μ P choices j0 χ b budget (fun _=>1)
    (integrable_const 1) (by simpa only [one_mul] using hbi) (2*(m:ℝ)*C0)
    (by simpa only [one_mul,integral_const,smul_eq_mul,mul_one] using hbb)
  have hci:Integrable (fun ω=>PairedRoughWordMoments.constant P choices j0 χ b (budget ω)) μ := by
    simpa only [one_mul] using hc.1
  have hcb:(∫ω,PairedRoughWordMoments.constant P choices j0 χ b (budget ω) ∂μ)≤
      PairedRoughWordMoments.constant P choices j0 χ b (2*(m:ℝ)*C0)*μ.real univ := by
    simpa only [one_mul,integral_const,smul_eq_mul,mul_one] using hc.2
  have hbound:∀ᵐ ω ∂μ,|G ω|^(2*b)≤PairedRoughWordMoments.constant P choices j0 χ b (budget ω)*K^(2*b) := by
    filter_upwards [hgeom] with ω hω
    have ho(j:Fin m):|oldOffset ω j|^power≤budget ω*(age j)^degree := by
      have h:=NormalizedLeafOffsets.offset_le_budget age (oldOffset ω) power degree ha j
      exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [budget];linarith [hBn ω]) (rpow_nonneg (ha j).le _))
    have hn(j:Fin m):|newOffset ω j|^power≤budget ω*(age j)^degree := by
      have h:=NormalizedLeafOffsets.offset_le_budget age (newOffset ω) power degree ha j
      exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [budget];linarith [hBo ω]) (rpow_nonneg (ha j).le _))
    have hmix(j:Fin m):|(if choose j then newMean ω else oldMean ω) (leaf j)-ControlledProfile.mean Λ (u ω) (d0 ω)
      ((if choose j then ηNew else ηOld),(target (leaf j),center (leaf j)))|^power≤budget ω*(age j)^degree := by
      split_ifs <;> first |exact hn j|exact ho j
    have hh:=PairedRoughWordMoments.even_moment P Λ (u ω) (d0 ω) θ ηOld ηNew
      (fun j=>if choose j then ηNew else ηOld) σ target center hσ hσ1 hages q hq lo hi hlo hlohi hstop hdisjoint
      (D ω) (hD ω) (newMean ω) (oldMean ω) (rootMean ω) (fun j=>if choose j then newMean ω else oldMean ω)
      g leaf hnative ht choices hnd chosen hchosen j0 F hFm hA0 hν hχ hχβ (hbudget ω) hf hfb b hb0 hmix (ho j0) (hn j0)
    dsimp only at hh
    have hbpoint:|G ω|^(2*b)≤PairedRoughWordMoments.constant P choices j0 χ b (budget ω)*
      ((∏j,scoreVariance (familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi j) (D ω j))*
        VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) 1*
        ∏j,leafScale P choices j0 χ lo hi target leaf chosen j)^(2*b) := by convert! hh.2.2 using 1
    apply hbpoint.trans
    apply mul_le_mul_of_nonneg_left _ (PairedRoughWordMoments.constant_nonneg P choices j0 χ b (hbudget ω))
    rw [←pow_abs_two_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) hω _
  have hgi:Integrable (fun ω=>|G ω|^(2*b)) μ:=(hci.mul_const (K^(2*b))).mono'
    ((continuous_abs.measurable.comp hG).pow_const _).aestronglyMeasurable
    (by filter_upwards [hbound] with ω hω;simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hω)
  refine ⟨hgi,?_⟩
  have hfinal:(∫ω,|G ω|^(2*b) ∂μ)≤
      (PairedRoughWordMoments.constant P choices j0 χ b (2*(m:ℝ)*C0)*μ.real univ)*K^(2*b) := by
    apply (integral_mono_ae hgi (hci.mul_const (K^(2*b))) hbound).trans
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hcb (pow_nonneg hK _)
  convert! hfinal using 1 <;>ring

end SHE.PairedRoughVaryingMoments
