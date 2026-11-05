module
public import SHE.BrownianConditionalIncrement
public import Mathlib.Data.Finset.Max
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.OrderedIncrementIndependence
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable{Ω:Type*}[MeasurableSpace Ω]
variable(μ:Measure Ω)[IsProbabilityMeasure μ]

/-- Successive independence from the entire preceding sigma algebra
implies joint independence, with the initial sigma algebra retained as
index zero. This is a finite-cylinder induction, not pairwise reasoning. -/
theorem ordered_sigma (m:ℕ→MeasurableSpace Ω)
    (hi:∀k,Indep (m (k+1)) (⨆j≤k,m j) μ):iIndep m μ:=by
  classical
  apply (iIndep_iff m μ).mpr
  intro s
  induction s using Finset.induction_on_max with
  | empty =>
    intro f hf
    simp
  | insert a s hlt ih =>
    intro f hf
    have ha:a∉s:=fun hh=>Nat.lt_irrefl a (hlt a hh)
    by_cases hz:a=0
    · subst a
      have hs:s=∅:=Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>Nat.not_lt_zero i (hlt i hi))
      simp [hs]
    · obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hz
      have hm:MeasurableSet[⨆j≤k,m j] (⋂j∈s,f j):=by
        apply s.measurableSet_biInter
        intro j hj
        have hjk:j≤k:=Nat.le_of_lt_succ (hlt j hj)
        have hjle:m j≤⨆i≤k,m i:=le_iSup_of_le j (le_iSup_of_le hjk le_rfl)
        exact hjle (f j) (hf j (Finset.mem_insert_of_mem hj))
      have he:=((hi k).indepSet_of_measurableSet
        (hf (k+1) (Finset.mem_insert_self _ _)) hm).measure_inter_eq_mul
      rw [Finset.set_biInter_insert,he,ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)),Finset.prod_insert ha]

variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(H:ℝ≥0)
variable{n:ℕ}(X:Fin n→ℝ≥0→Ω→ℝ)(G:Matrix (Fin n) (Fin n) ℝ)
variable(T:ℕ→ℝ≥0)

def sigma:ℕ→MeasurableSpace Ω
  | 0=>𝓕 (T 0)
  | k+1=>(inferInstance:MeasurableSpace (WordRecursion.State n)).comap
      (fun ω=>WithLp.toLp 2 (fun i=>X i (T (k+1)) ω-X i (T k) ω))

/-- Actual Brownian increment sigma algebras along an ordered grid are
jointly independent of the ORIGINAL initial past sigma algebra. -/
theorem brownian_grid
    (hBrown:FiniteBrownianLawOn 𝓕 μ H X G)
    (hX:∀i t,Measurable[𝓕 t] (X i t))
    (hT:Monotone T)(hTH:∀k,T k≤H):iIndep (sigma 𝓕 X T) μ:=by
  have hm(k:ℕ):sigma 𝓕 X T k≤𝓕 (T k):=by
    cases k with
    | zero =>exact le_rfl
    | succ k =>
      change (inferInstance:MeasurableSpace (WordRecursion.State n)).comap
        (fun ω=>WithLp.toLp 2 (fun i=>X i (T (k+1)) ω-X i (T k) ω))≤𝓕 (T (k+1))
      letI:MeasurableSpace Ω:=𝓕 (T (k+1))
      apply Measurable.comap_le
      apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
      apply measurable_pi_iff.mpr
      intro i
      exact (hX i (T (k+1))).sub ((hX i (T k)).mono (𝓕.mono (hT (Nat.le_succ k))) le_rfl)
  apply ordered_sigma μ
  intro k
  have hi:=hBrown.2 (T k) (T (k+1)) (hT (Nat.le_succ k)) (hTH (k+1))
  apply indep_of_indep_of_le_right hi
  exact iSup_le (fun j=>iSup_le (fun hj=>(hm j).trans (𝓕.mono (hT hj))))
end SHE.OrderedIncrementIndependence
