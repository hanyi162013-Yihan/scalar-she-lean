module

public import SHE.HistoryProductMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.HistoryProductMeasure
open Set Filter MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories PhysicalScoreChain
  PhysicalParentGeometry
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P]

theorem root_assemble (k : ℕ) (p : P × (Fin k → ℝ × HeatCircle)) :
    rootParameter k (assemble k p)=p.1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (p.1,fun i => p.2 i.succ)

theorem nodes_assemble (k : ℕ) (p : P × (Fin k → ℝ × HeatCircle)) :
    nodes k (assemble k p)=p.2 := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (p.1,fun i => p.2 i.succ)) j

theorem root_separated (k : ℕ) (p : P × ((Fin k → ℝ) × (Fin k → HeatCircle))) :
    rootParameter k (separated k p)=p.1 := root_assemble k _

theorem nodes_separated (k : ℕ) (p : P × ((Fin k → ℝ) × (Fin k → HeatCircle))) :
    nodes k (separated k p)=fun i => (p.2.1 i,p.2.2 i) := nodes_assemble k _

theorem replaceSpace_separated (k : ℕ) (p : P) (t : Fin k → ℝ)
    (x₀ x : Fin k → HeatCircle) :
    replaceSpace k (separated k (p,t,x₀)) x=separated k (p,t,x) := by
  rw [← separated_eq_replace]
  simp only [root_separated,nodes_separated]

theorem separated_measurable (k : ℕ) : Measurable (separated (P := P) k) := by
  exact (assemble_measurable k).comp (measurable_fst.prodMk
    (Measurable.of_eval (fun i =>
      ((measurable_pi_apply i).comp measurable_snd.fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd.snd))))

theorem replaceSpace_measurable (k : ℕ) (p : History P k) : Measurable (replaceSpace k p) := by
  have hm : Measurable (fun x : Fin k → HeatCircle =>
      (rootParameter k p,fun i => ((nodes k p i).1,x i))) :=
    measurable_const.prodMk (Measurable.of_eval (fun i => measurable_const.prodMk (measurable_pi_apply i)))
  have he : (fun x : Fin k → HeatCircle => assemble k
      (rootParameter k p,fun i => ((nodes k p i).1,x i)))=replaceSpace k p := by
    funext x
    exact separated_eq_replace k p x
  rw [← he]
  exact (assemble_measurable k).comp hm

/-- Almost-everywhere history statements genuinely disintegrate over
the original initial parameter, all original time variables, and every
insertion location. No separately AE fixed-frame statement is evaluated
at a random diagonal. -/
theorem ae_spatial_sections (R : ReferenceData) (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ)
    {F : History P k → Prop} (hF : ∀ᵐ p ∂historyMeasure R μ k, F p) :
    ∀ᵐ p ∂μ, ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
      ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      F (separated k (p,t,x)) := by
  have hh := (separated_measurePreserving R μ k).quasiMeasurePreserving.ae hF
  filter_upwards [Measure.ae_ae_of_ae_prod hh] with p hp
  exact Measure.ae_ae_of_ae_prod hp

theorem ae_replaceSpace_sections (R : ReferenceData) (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ)
    {F : History P k → Prop} (hF : ∀ᵐ p ∂historyMeasure R μ k, F p) :
    ∀ᵐ p ∂μ, ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
      ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      F (replaceSpace k (separated k (p,t,fun _ => 0)) x) := by
  filter_upwards [ae_spatial_sections R μ k hF] with p hp
  filter_upwards [hp] with t ht
  simpa only [replaceSpace_separated] using ht

end SHE.HistoryProductMeasure
