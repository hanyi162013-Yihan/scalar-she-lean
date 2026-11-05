module

public import SHE.BoundedVectorIntegral
public import SHE.PastItoAlgebra
public import SHE.TwoChannelItoRows
public import SHE.StoppedIntegralVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section
namespace SHE.FiniteReferenceSplice
open Set MeasureTheory PredictableL2 StoppedItoInputs PastItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {n : ℕ} (v : ℝ≥0) (R S : Fin n → Process (E:=C) 𝓕 μ H)

def rows (i : Fin n) : Process (E:=C) 𝓕 μ H :=
  stop 𝓕 μ H (v:ℝ) (R i)+post 𝓕 μ H v (S i)

theorem stopped_rows (i : Fin n) (t : ℝ≥0) :
    stop 𝓕 μ H (t:ℝ) (rows 𝓕 μ H v R S i)=
      stop 𝓕 μ H (min (t:ℝ) (v:ℝ)) (R i)+stop 𝓕 μ H (t:ℝ) (post 𝓕 μ H v (S i)) := by
  rw [rows,TwoChannelItoRows.stop_add,StoppedIntegralVersions.stop_stop]

/-- The old and replacement rows occupy disjoint original-noise time
intervals. Their bound does not require independence of either field. -/
theorem rows_bound (K L : Fin n → ℝ) (hK : ∀ i,0≤K i) (hL : ∀ i,0≤L i)
    (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖R i p‖^2≤K i)
    (hS : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖S i p‖^2≤L i) (i : Fin n) :
    ∀ᵐ p ∂energyMeasure μ H,‖rows 𝓕 μ H v R S i p‖^2≤K i+L i := by
  filter_upwards [hR i,hS i,stop_ae 𝓕 μ H (v:ℝ) (R i),post_ae 𝓕 μ H v (S i),
    ae_eq_of_ae_eq_trim (Lp.coeFn_add (stop 𝓕 μ H (v:ℝ) (R i)) (post 𝓕 μ H v (S i)))]
    with p hR hS hstop hpost hadd
  change ‖(stop 𝓕 μ H (v:ℝ) (R i)+post 𝓕 μ H v (S i)) p‖^2≤_
  rw [hadd]
  simp only [Pi.add_apply,hstop,hpost,indicator_apply,before,mem_ofPred_eq,NNReal.coe_lt_coe]
  by_cases hrv : p.1<v
  · simp only [hrv,ite_true,not_lt.mpr hrv.le,ite_false,add_zero]
    linarith [hL i]
  · by_cases hvr : v<p.1
    · simp only [hrv,hvr,ite_true,ite_false,zero_add]
      linarith [hK i]
    · simp only [hrv,hvr,ite_false,zero_add,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact add_nonneg (hK i) (hL i)

variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Exact frozen-reference representation after the past time. The
initial vector is still deterministic; its random F_v value is the
actual PRE-v part of the same original integral. -/
theorem integral_after_past (z : WordRecursion.State n) (t : ℝ≥0) (hvt : v≤t) :
    StandardFiniteIto.vectorIntegral 𝓕 μ H J z (rows 𝓕 μ H v R S) t =ᵐ[μ]
      fun ω => StandardFiniteIto.vectorIntegral 𝓕 μ H J z R v ω+
        WithLp.toLp 2 (fun i => J.integral (stop 𝓕 μ H (t:ℝ) (post 𝓕 μ H v (S i))) ω) := by
  have he := ae_all_iff.mpr (fun i : Fin n => Lp.coeFn_add
    (J.integral (stop 𝓕 μ H (v:ℝ) (R i)))
    (J.integral (stop 𝓕 μ H (t:ℝ) (post 𝓕 μ H v (S i)))))
  filter_upwards [he] with ω hω
  apply PiLp.ext
  intro i
  change z i+J.integral (stop 𝓕 μ H (t:ℝ) (rows 𝓕 μ H v R S i)) ω=
    (z i+J.integral (stop 𝓕 μ H (v:ℝ) (R i)) ω)+
      J.integral (stop 𝓕 μ H (t:ℝ) (post 𝓕 μ H v (S i))) ω
  rw [stopped_rows,map_add,min_eq_right (show (v:ℝ)≤(t:ℝ) by exact_mod_cast hvt),hω i]
  simp only [Pi.add_apply]
  ring

/-- Both actual and frozen-reference observations form one finite
vector driven by the SAME scalar integral. -/
def jointRows : Fin (n+n) → Process (E:=C) 𝓕 μ H := Fin.append R (rows 𝓕 μ H v R S)

def jointInitial (z : WordRecursion.State n) : WordRecursion.State (n+n) :=
  WithLp.toLp 2 (Fin.append (fun i => z i) (fun i => z i))

def value (z : WordRecursion.State n) : ℝ≥0×Ω → WordRecursion.State (n+n) :=
  BoundedVectorIntegral.value 𝓕 μ H J (jointInitial z) (jointRows 𝓕 μ H v R S)

/-- Ordinary finite-dimensional Ito applies to the actual/frozen pair
once the literal positive-prefix row caps are proved. No random-initial
or independently restarted Ito formula is invoked. -/
theorem finiteItoInput (hH : (H:ℝ)≤1) (hH0 : 0<H)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J)
    (z : WordRecursion.State n) (K L : Fin n → ℝ) (hK : ∀ i,0≤K i) (hL : ∀ i,0≤L i)
    (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖R i p‖^2≤K i)
    (hS : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖S i p‖^2≤L i)
    (c : ℝ≥0) (hvc : v≤c) (hcH : c≤H) :
    ∃ N : (ℝ→WordRecursion.State (n+n)→ℝ)→Ω→ℝ,
      (∀ G,Integrable (N G) μ ∧ (∫ ω,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ (fun ω t => value 𝓕 μ H v R S J z (t.toNNReal,ω))
        (StandardFiniteIto.rowCovariance 𝓕 μ H (jointRows 𝓕 μ H v R S)) v c N := by
  let cap : Fin (n+n)→ℝ := Fin.append K (fun i => K i+L i)
  have hcap : ∀ i,0≤cap i := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [cap,Fin.append_left] using hK j
    · simpa only [cap,Fin.append_right] using add_nonneg (hK j) (hL j)
  have hbnd : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖jointRows 𝓕 μ H v R S i p‖^2≤cap i := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [jointRows,cap,Fin.append_left] using hR j
    · simpa only [jointRows,cap,Fin.append_right] using rows_bound 𝓕 μ H v R S K L hK hL hR hS j
  let Y := value 𝓕 μ H v R S J z
  have hY := BoundedVectorIntegral.predictable_value 𝓕 μ H J (jointInitial z)
    (jointRows 𝓕 μ H v R S) hH hH0 hnull B hBDG cap hcap hbnd
  let N := fun G ω => FiniteItoNoise.noise 𝓕 μ H Y hY (jointRows 𝓕 μ H v R S) J v c G ω
  refine ⟨N,fun G => ⟨FiniteItoNoise.noise_integrable 𝓕 μ H Y hY _ J v c G,
    FiniteItoNoise.noise_centered 𝓕 μ H Y hY _ J v c G⟩,?_⟩
  exact StandardFiniteIto.finiteItoInput 𝓕 μ H J hJ (jointRows 𝓕 μ H v R S) (jointInitial z)
    Y hY (BoundedVectorIntegral.continuous_value 𝓕 μ H J (jointInitial z) _ hH0)
    (BoundedVectorIntegral.integral_representation 𝓕 μ H J (jointInitial z) _ hH hH0 B hBDG cap hcap hbnd)
    v.2 (by exact_mod_cast hvc) (by exact_mod_cast hcH)

end SHE.FiniteReferenceSplice
