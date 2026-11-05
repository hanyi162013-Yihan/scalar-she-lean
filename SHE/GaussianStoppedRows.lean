module

public import SHE.GaussianMatrixIto
public import SHE.SingularVectorIntegral
public import SHE.SingularInputBounds
public import SHE.StoppedInputAlgebra
public import SHE.PastItoAlgebra

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.GaussianStoppedRows
open Set MeasureTheory ProbabilityTheory PredictableL2 StoppedItoInputs PastItoInputs
open SingularInputBounds GaussianMatrixCurve SmoothCylinders GaussianConvolution
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) {n : ℕ} (R : Fin n → Process (E:=C) 𝓕 μ H)

def rows (i : Fin n) : Process (E:=C) 𝓕 μ H :=
  stop 𝓕 μ H (b:ℝ) (post 𝓕 μ H v (R i))

theorem rows_ae (i : Fin n) : rows 𝓕 μ H v b R i =ᵐ[energyMeasure μ H]
    fun p => if v<p.1 ∧ p.1<b then R i p else 0 := by
  filter_upwards [stop_ae 𝓕 μ H (b:ℝ) (post 𝓕 μ H v (R i)),
    post_ae 𝓕 μ H v (R i)] with p hs hp
  change stop 𝓕 μ H (b:ℝ) (post 𝓕 μ H v (R i)) p = _
  rw [hs]
  simp only [indicator_apply,before,mem_setOf_eq,NNReal.coe_lt_coe]
  rw [hp]
  by_cases hpb : p.1<b <;> by_cases hvp : v<p.1 <;> simp [hpb,hvp]

theorem rows_bound (K : Fin n → ℝ) (hK : ∀ i, 0≤K i)
    (hR : ∀ i, Bound 𝓕 μ H b (K i) (R i)) (i : Fin n) :
    Bound 𝓕 μ H b (K i) (rows 𝓕 μ H v b R i) := by
  filter_upwards [rows_ae 𝓕 μ H v b R i,hR i] with p hp hr hpb
  rw [hp]
  split_ifs
  · exact hr hpb
  · simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      mul_nonneg (hK i) (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hpb)) (-(1/2:ℝ)))

variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) (z : WordRecursion.State n)

def terminal (ω : Ω) : WordRecursion.State n :=
  WithLp.toLp 2 (fun i => z i + J.integral (rows 𝓕 μ H v b R i) ω)

local notation "Y" => SingularVectorIntegral.value 𝓕 μ H b J z (rows 𝓕 μ H v b R)

include μ in
theorem stop_rows (t : ℝ) (i : Fin n) :
    stop 𝓕 μ H t (rows 𝓕 μ H v b R i) =
      stop 𝓕 μ H (min t (b:ℝ)) (post 𝓕 μ H v (R i)) := by
  exact StoppedInputAlgebra.stop_stop 𝓕 μ H t (b:ℝ) _

theorem stop_at_past (i : Fin n) : stop 𝓕 μ H (v:ℝ) (rows 𝓕 μ H v b R i)=0 := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [stop_ae 𝓕 μ H (v:ℝ) (rows 𝓕 μ H v b R i),rows_ae 𝓕 μ H v b R i,
    ae_eq_of_ae_eq_trim (Lp.coeFn_zero C 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hs hr hz
  rw [hs,hz]
  simp only [indicator_apply,before,mem_setOf_eq,NNReal.coe_lt_coe,Pi.zero_apply]
  rw [hr]
  by_cases hp : p.1<v
  · have hn : ¬v<p.1 := not_lt_of_ge hp.le
    simp only [ite_eq_left hp,hn,false_and,ite_eq_right (not_false)]
  · simp only [if_neg hp]

theorem representation (hbH : b≤H) (hb0 : 0<b)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (K : Fin n → ℝ) (hK : ∀ i,0≤K i) (hR : ∀ i,Bound 𝓕 μ H b (K i) (R i))
    (t : ℝ≥0) :
    (fun ω => Y (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z (rows 𝓕 μ H v b R) t := by
  have he := ae_all_iff.mpr (fun i => SingularStoppedVersion.version_ae 𝓕 μ H b J
    (rows 𝓕 μ H v b R i) hbH hb0 B hBDG (hK i) (rows_bound 𝓕 μ H v b R K hK hR i) t)
  filter_upwards [he] with ω hω
  apply PiLp.ext
  intro i
  change z i+SingularStoppedVersion.version 𝓕 μ H b J (rows 𝓕 μ H v b R i) t ω=_
  rw [hω i]
  simp only [StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp,rows,StoppedInputAlgebra.stop_stop,
    NNReal.coe_min,min_assoc,min_self]

/-- Actual finite original-J rows with a deterministic Gram curve have
that Gaussian transition on every original past event. Continuous versions
and terminal singularities are discharged from the ordinary BDG package. -/
theorem conditional_smooth (hbH : b≤H) (hb0 : 0<b)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (K : Fin n → ℝ) (hK : ∀ i,0≤K i) (hR : ∀ i,Bound 𝓕 μ H b (K i) (R i))
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J)
    (W : Curve n) (hv : W.left=(v:ℝ)) (hb : W.right=(b:ℝ))
    (hcov : ∀ᵐ ω ∂μ,∀ᵐ t : ℝ,t∈Ioo W.left W.right →
      StandardFiniteIto.rowCovariance 𝓕 μ H (rows 𝓕 μ H v b R) ω t=W.density t)
    {F : WordRecursion.State n→ℝ} (hF : BoundedSmooth F)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫ ω in A, F (terminal 𝓕 μ H v b R J z ω) ∂μ) =
      μ.real A * gaussianAverage (W.path W.left).val F z := by
  have hY := SingularVectorIntegral.predictable_value 𝓕 μ H b J z (rows 𝓕 μ H v b R)
    hbH hb0 hnull B hBDG K hK (rows_bound 𝓕 μ H v b R K hK hR)
  have hrep := representation 𝓕 μ H v b R J z hbH hb0 B hBDG K hK hR
  have ht := GaussianMatrixIto.transition_on_past_event 𝓕 μ H J (rows 𝓕 μ H v b R) z Y hY
    hJ hlocal (SingularVectorIntegral.continuous_value 𝓕 μ H b J z _ hb0)
    (fun t _ => hrep t) W v b hv hb hbH hcov hF A hA
  have hstart : (fun ω => Y (v,ω)) =ᵐ[μ] fun _ => z := by
    filter_upwards [hrep v,Lp.coeFn_zero ℝ 2 μ] with ω hy hz
    rw [hy]
    apply PiLp.ext
    intro i
    change z i + J.integral (stop 𝓕 μ H (v:ℝ) (rows 𝓕 μ H v b R i)) ω = z i
    rw [stop_at_past,map_zero]
    exact add_eq_left.mpr hz
  have hend : (fun ω => Y (b,ω)) =ᵐ[μ] terminal 𝓕 μ H v b R J z := by
    filter_upwards [hrep b] with ω hy
    rw [hy]
    apply PiLp.ext
    intro i
    change z i+J.integral (stop 𝓕 μ H (b:ℝ) (rows 𝓕 μ H v b R i)) ω=_
    simp only [rows,StoppedInputAlgebra.stop_stop,min_self,terminal,WithLp.ofLp_toLp]
  rw [integral_congr_ae (ae_restrict_of_ae (hend.mono (fun _ h => (congrArg F h).symm))),ht]
  calc
    _ = ∫ _ω : Ω in A, GaussianMatrixCurve.backward W F W.left z ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hstart] with ω hω
      rw [hω]
    _ = _ := by simp [GaussianMatrixCurve.backward,Measure.real,smul_eq_mul]

end SHE.GaussianStoppedRows
