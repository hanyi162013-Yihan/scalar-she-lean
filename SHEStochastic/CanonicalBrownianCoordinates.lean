module

public import SHEStochastic.CanonicalBrownianChannels
public import SHEStochastic.CenteredGaussianFiniteLaw
public import SHEStochastic.FiniteScalarIto
public import SHE.BrownianFiniteCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.CanonicalBrownianCoordinates
open MeasureTheory ProbabilityTheory SHE
open CanonicalBrownianChannels
open scoped NNReal ENNReal
local notation "μ" => CanonicalBrownianMeasure.measure

def past (s : ℝ≥0) (ω : Sample) (p : ℕ×{r : ℝ≥0 // r ≤ s}) : ℝ := value p.1 p.2 ω

def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace Sample) where
  seq s := MeasurableSpace.comap (past s) inferInstance
  mono' s t hst := by
    let f := fun x : (ℕ×{r : ℝ≥0 // r ≤ t} → ℝ) =>
      fun p : ℕ×{r : ℝ≥0 // r ≤ s} => x (p.1,⟨p.2,hst.trans' p.2.property⟩)
    have hm : Measurable f := measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
    have he : past s=f ∘ past t := rfl
    change MeasurableSpace.comap (past s) inferInstance ≤ MeasurableSpace.comap (past t) inferInstance
    rw [he,←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hm.comap_le
  le' s := by
    have hm : Measurable (past s) := by
      apply measurable_pi_iff.mpr
      intro p
      exact measurable_value p.1 p.2
    exact hm.comap_le

theorem adapted (i : ℕ) (t : ℝ≥0) : Measurable[filtration t] (value i t) := by
  have hp : Measurable[filtration t] (past t) := measurable_iff_comap_le.mpr le_rfl
  exact (measurable_pi_apply (i,⟨t,le_rfl⟩)).comp hp

/-- The raw coordinate vector has its exact finite Brownian law.
Every repeated channel and every individual observation time is retained. -/
theorem finite_law {n : ℕ} (a : Fin n → ℕ) (t : Fin n → ℝ≥0) (ht : ∀ i,t i ≤ 1) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => value (a i) (t i) ω))
      (multivariateGaussian (0 : GaussianIncrement.State n) (BrownianFiniteCovariance.matrix a t)) μ := by
  classical
  have hg := difference_gaussian (fun i : Fin n => time (a i) (t i)) (fun i : Fin n => start (a i))
  let I : Finset (Fin n) := Finset.univ
  let L0 : (I → ℝ) →L[ℝ] (Fin n → ℝ) := {
    toFun := fun x i => x ⟨i,by simp [I]⟩
    map_add' := by intros;ext;simp
    map_smul' := by intros;ext;simp }
  let L : (I → ℝ) →L[ℝ] GaussianIncrement.State n :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp L0
  have hX : HasGaussianLaw (fun ω => WithLp.toLp 2 (fun i => value (a i) (t i) ω)) μ := by
    have hh := (hg.hasGaussianLaw I).map L
    exact hh
  apply CenteredGaussianFiniteLaw.law_state _ hX _ (BrownianFiniteCovariance.posSemidef a t)
    (fun i => mean_value (a i) (t i))
  intro i j
  have hi : min (t i : ℝ) 1=t i := min_eq_left (by exact_mod_cast ht i)
  have hj : min (t j : ℝ) 1=t j := min_eq_left (by exact_mod_cast ht j)
  rw [covariance_value,hi,hj]
  simp only [BrownianFiniteCovariance.matrix,NNReal.coe_min]
  split_ifs <;> simp

/-- Every finite future increment vector is independent of the full
natural past of all countably many channels. This uses joint Gaussianity
and exact cross-covariance, without a finite-past restriction. -/
theorem future_independent (n : ℕ) (a : Fin n → ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => (WithLp.toLp 2
      (fun i => value (a i) t ω-value (a i) s ω) : GaussianIncrement.State n)) inferInstance) (filtration s) μ := by
  let X := fun i : Fin n => fun ω : Sample => value (a i) t ω-value (a i) s ω
  let Y := fun p : ℕ×{r : ℝ≥0 // r ≤ s} => value p.1 p.2.val
  let hi := Sum.elim (fun i : Fin n => time (a i) t)
    (fun p : ℕ×{r : ℝ≥0 // r ≤ s} => time p.1 p.2)
  let lo := Sum.elim (fun i : Fin n => time (a i) s)
    (fun p : ℕ×{r : ℝ≥0 // r ≤ s} => start p.1)
  have hG : IsGaussianProcess (Sum.elim X Y) μ :=
    (difference_gaussian hi lo).congr (fun i => Filter.Eventually.of_forall (fun ω => by
      cases i <;> dsimp only [hi,lo,Sum.elim,X,Y,value] <;> abel))
  have hCov (i : Fin n) (p : ℕ×{r : ℝ≥0 // r ≤ s}) : cov[X i,Y p;μ]=0 := by
    rw [covariance_fun_sub_left (memLp_value (a i) t) (memLp_value (a i) s) (memLp_value p.1 p.2)]
    rw [covariance_value,covariance_value]
    by_cases h : a i=p.1
    · have hs : min (p.2.val : ℝ) 1 ≤ min (s : ℝ) 1 :=
        min_le_min_right _ (by exact_mod_cast p.2.property)
      have ht : min (p.2.val : ℝ) 1 ≤ min (t : ℝ) 1 :=
        min_le_min_right _ (by exact_mod_cast p.2.property.trans hst)
      simp only [if_pos h,min_eq_right hs,min_eq_right ht,sub_self]
    · simp only [if_neg h,sub_self]
  have hInd := hG.indepFun_of_covariance_eq_zero
    (fun i => ((measurable_value (a i) t).sub (measurable_value (a i) s)).aemeasurable)
    (fun p => (measurable_value p.1 p.2).aemeasurable) hCov
  have hVec := hInd.comp (φ := WithLp.toLp 2) (ψ := id) (WithLp.measurable_toLp _ _) measurable_id
  exact (IndepFun_iff_Indep _ _ _).mp hVec

/-- An actually constructed native coordinate family on the unit
horizon, prior to taking continuous null-complete versions. -/
def coordinates : FiniteScalarIto.Coordinates filtration μ 1 ℕ where
  W := value
  adapted := adapted
  law n a := ⟨fun t ht => finite_law a t ht,fun s t hst _ => future_independent n a s t hst⟩

end SHEStochastic.CanonicalBrownianCoordinates
