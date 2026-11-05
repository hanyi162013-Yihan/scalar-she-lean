module
public import SHE.OrderedGridCover
public import SHE.FiniteCylinderIndependence
public import SHE.BrownianConditionalGrid
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.BrownianFutureCylinders
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P ι:Type*}[MeasurableSpace Ω][MeasurableSpace P][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(X:ι→ℝ≥0→Ω→ℝ)
variable(hX:∀i t,Measurable[𝓕 t] (X i t))
variable(hBrown:∀n (a:Fin n→ι),FiniteBrownianLawOn 𝓕 μ H (fun i=>X (a i))
  (fun i j=>if a i=a j then 1 else 0))

def cumulative {n:ℕ}(d:ℕ→WordRecursion.State n)(k:ℕ):WordRecursion.State n:=
  ∑j∈Finset.range k,d j

private theorem cumulative_increments{n:ℕ}(Y:Fin n→ℝ≥0→Ω→ℝ)(T:ℕ→ℝ≥0)(ω:Ω)(k:ℕ):
    cumulative (BrownianConditionalGrid.increments Y T ω) k=
      WithLp.toLp 2 (fun i=>Y i (T k) ω-Y i (T 0) ω):=by
  induction k with
  | zero =>ext i;simp[cumulative]
  | succ k ih =>
    rw [cumulative,Finset.sum_range_succ]
    change cumulative (BrownianConditionalGrid.increments Y T ω) k+_= _
    rw[ih]
    ext i
    simp only[BrownianConditionalGrid.increments,PiLp.add_apply,WithLp.equiv_symm_apply]
    abel

include hX hBrown in
/-- Arbitrary finite future observations are independent of the actual
restart past, obtained by decoding one genuine ordered increment grid. -/
theorem finite (v:ℝ≥0)(hv:v≤H){n:ℕ}(a:Fin n→ι)(t:Fin n→ℝ≥0)
    (ht:∀i,v≤t i∧t i≤H)(Z:Ω→P)(hZ:Measurable[𝓕 v] Z):
    IndepFun Z (fun ω=>fun i=>X (a i) (t i) ω-X (a i) v ω) μ:=by
  classical
  obtain ⟨T,hT,hT0,hTH,hcover⟩:=OrderedGridCover.exists_cover v H hv
    (Finset.univ.image t) (by simpa using ht)
  choose k hk using (fun i:Fin n=>hcover (t i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
  have hz:Measurable[𝓕 (T 0)] Z:=hT0.symm ▸ hZ
  have hi:=BrownianConditionalGrid.independent 𝓕 μ H (fun i=>X (a i))
    (fun i j=>if a i=a j then 1 else 0) T (hBrown n a) (fun i=>hX (a i)) hT hTH Z hz
  let decode:(ℕ→WordRecursion.State n)→(Fin n→ℝ):=
    fun d i=>(cumulative d (k i)) i
  have hd:Measurable decode:=by
    apply measurable_pi_iff.mpr
    intro i
    exact (show Measurable (fun z:WordRecursion.State n=>z i) by fun_prop).comp
      (Finset.measurable_sum _ (fun j _=>measurable_pi_apply j))
  have hh:=hi.comp measurable_id hd
  have he:decode ∘ BrownianConditionalGrid.increments (fun i=>X (a i)) T=
      (fun ω=>fun i=>X (a i) (t i) ω-X (a i) v ω):=by
    funext ω i
    dsimp[decode,Function.comp_def]
    rw[cumulative_increments,hk,hT0]
  simpa only[Function.comp_id,Function.id_comp,he] using hh

include hX hBrown in
/-- The whole future coordinate sigma algebra is independent of the
restart past; this avoids any uncountable intersection of AE events. -/
theorem full {κ:Type*}(v:ℝ≥0)(hv:v≤H)(a:κ→ι)(t:κ→ℝ≥0)
    (ht:∀i,v≤t i∧t i≤H)(Z:Ω→P)(hZ:Measurable[𝓕 v] Z):
    IndepFun Z (fun ω=>fun i=>X (a i) (t i) ω-X (a i) v ω) μ:=by
  classical
  apply FiniteCylinderIndependence.full μ Z _ (hZ.mono (𝓕.le _) le_rfl)
    (fun i=>((hX (a i) (t i)).mono (𝓕.le _) le_rfl).sub
      ((hX (a i) v).mono (𝓕.le _) le_rfl))
  intro s
  let e:=Fintype.equivFin s
  have hi:=finite 𝓕 μ H X hX hBrown v hv (fun i=>(a (e.symm i).val))
    (fun i=>t (e.symm i).val) (fun i=>ht _) Z hZ
  let decode:(Fin (Fintype.card s)→ℝ)→(s→ℝ):=fun f i=>f (e i)
  have hd:Measurable decode:=measurable_pi_iff.mpr (fun i=>measurable_pi_apply (e i))
  simpa only[Function.comp_def,decode,Equiv.symm_apply_apply,id_eq,Pi.sub_apply] using hi.comp measurable_id hd
end SHE.BrownianFutureCylinders
