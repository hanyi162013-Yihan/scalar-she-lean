module

public import SHE.SingularInputBounds
public import SHE.SingularVectorIntegral
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace SHE.SingularReferenceSplice
open Set MeasureTheory PredictableL2 StoppedItoInputs PastItoInputs SingularInputBounds
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b v : ℝ≥0)
variable {n : ℕ} (R S : Fin n→Process (E:=C) 𝓕 μ H)
variable (K L : Fin n→ℝ) (hK : ∀ i,0≤K i) (hL : ∀ i,0≤L i)
variable (hR : ∀ i:Fin n,∀ᵐ p∂energyMeasure μ H,p.1≤b→‖R i p‖^2≤K i*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
variable (hS : ∀ i:Fin n,∀ᵐ p∂energyMeasure μ H,p.1≤b→‖S i p‖^2≤L i*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))

def cap : Fin (n+n)→ℝ:=Fin.append K (fun i=>K i+L i)

include hK hL in
theorem cap_nonneg (i : Fin (n+n)) : 0≤cap K L i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [cap,Fin.append_left] using hK j
  · simpa only [cap,Fin.append_right] using add_nonneg (hK j) (hL j)

include hK hL hR hS in
theorem splice_bound (i : Fin n) : Bound (C:=C) 𝓕 μ H b (K i+L i) (FiniteReferenceSplice.rows 𝓕 μ H v R S i) := by
  filter_upwards [hR i,hS i,stop_ae 𝓕 μ H (v:ℝ) (R i),post_ae 𝓕 μ H v (S i),
    ae_eq_of_ae_eq_trim (Lp.coeFn_add (stop 𝓕 μ H (v:ℝ) (R i)) (post 𝓕 μ H v (S i)))]
    with p hR hS hstop hpost hadd hp
  have hφ : 0≤((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)):=Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hp)) _
  change ‖(stop 𝓕 μ H (v:ℝ) (R i)+post 𝓕 μ H v (S i)) p‖^2≤_
  rw [hadd]
  simp only [Pi.add_apply,hstop,hpost,indicator_apply,before,mem_ofPred_eq,NNReal.coe_lt_coe]
  by_cases hrv : p.1<v
  · simp only [hrv,ite_true,not_lt.mpr hrv.le,ite_false,add_zero]
    nlinarith [hR hp,mul_nonneg (hL i) hφ]
  · by_cases hvr : v<p.1
    · simp only [hrv,hvr,ite_true,ite_false,zero_add]
      nlinarith [hS hp,mul_nonneg (hK i) hφ]
    · simp only [hrv,hvr,ite_false,zero_add,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact mul_nonneg (add_nonneg (hK i) (hL i)) hφ

def rows (i : Fin (n+n)) : Process (E:=C) 𝓕 μ H:=
  stop 𝓕 μ H (b:ℝ) (FiniteReferenceSplice.jointRows 𝓕 μ H v R S i)

include hK hL hR hS in
theorem rows_bound (i : Fin (n+n)) : Bound (C:=C) 𝓕 μ H b (cap K L i) (rows 𝓕 μ H b v R S i) := by
  apply stop_bound 𝓕 μ H b (cap_nonneg K L hK hL i)
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [SingularInputBounds.Bound,cap,FiniteReferenceSplice.jointRows,Fin.append_left] using hR j
  · simpa only [cap,FiniteReferenceSplice.jointRows,Fin.append_right] using splice_bound 𝓕 μ H b v R S K L hK hL hR hS j

variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) (z : WordRecursion.State n)

def value : ℝ≥0×Ω→WordRecursion.State (n+n):=
  SingularVectorIntegral.value 𝓕 μ H b J (FiniteReferenceSplice.jointInitial z) (rows 𝓕 μ H b v R S)

theorem continuous_value (hb0 : 0<b) (ω : Ω) : Continuous (fun t=>value 𝓕 μ H b v R S J z (t,ω)):=
  SingularVectorIntegral.continuous_value 𝓕 μ H b J _ _ hb0 ω

include hK hL hR hS in
theorem predictable_value (hbH : b≤H) (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B) :
    StronglyMeasurable[𝓕.predictable] (value 𝓕 μ H b v R S J z):=
  SingularVectorIntegral.predictable_value 𝓕 μ H b J _ _ hbH hb0 hnull B hBDG (cap K L)
    (cap_nonneg K L hK hL) (rows_bound 𝓕 μ H b v R S K L hK hL hR hS)

include hK hL hR hS in
/-- The singular continuous vector represents the ORIGINAL full-H J at
all times, because the actual endpoint rows are stopped at b. -/
theorem integral_representation (hbH : b≤H) (hb0 : 0<b)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B) (t : ℝ≥0) :
    (fun ω=>value 𝓕 μ H b v R S J z (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z)
        (rows 𝓕 μ H b v R S) t := by
  have he:=ae_all_iff.mpr (fun i=>SingularStoppedVersion.version_ae 𝓕 μ H b J
    (rows 𝓕 μ H b v R S i) hbH hb0 B hBDG (cap_nonneg K L hK hL i)
    (rows_bound 𝓕 μ H b v R S K L hK hL hR hS i) t)
  filter_upwards [he] with ω hω
  apply PiLp.ext
  intro i
  change (FiniteReferenceSplice.jointInitial z) i+SingularStoppedVersion.version 𝓕 μ H b J
    (rows 𝓕 μ H b v R S i) t ω=_
  rw [hω i]
  simp only [StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp,rows,StoppedInputAlgebra.stop_stop,
    NNReal.coe_min,min_assoc,min_self]

end SHE.SingularReferenceSplice
