module
public import SHE.PredictableSquareDominatedLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.PredictableBoundedTruncation
open Set MeasureTheory PredictableL2 Filter Topology
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(Q:Measure Ω)(H:ℝ≥0)
variable (g:Process (E:=C) 𝓕 Q H)

def raw(n:ℕ)(p:ℝ≥0×Ω):C:=if ‖g p‖≤(n:ℝ) then g p else 0

theorem raw_predictable(n:ℕ):StronglyMeasurable[𝓕.predictable] (raw 𝓕 Q H g n):=by
  unfold raw
  exact (Lp.stronglyMeasurable g).piecewise
    (measurableSet_le (Lp.stronglyMeasurable g).norm.measurable measurable_const) stronglyMeasurable_const

theorem raw_bound(n:ℕ)(p:ℝ≥0×Ω):‖raw 𝓕 Q H g n p‖≤(n:ℝ):=by
  unfold raw
  split_ifs with h
  · exact h
  · simpa only [norm_zero] using (Nat.cast_nonneg n:0≤(n:ℝ))

theorem raw_le(n:ℕ)(p:ℝ≥0×Ω):‖raw 𝓕 Q H g n p‖≤‖g p‖:=by
  unfold raw
  split_ifs
  · exact le_refl _
  · simpa only [norm_zero] using norm_nonneg (g p)

theorem raw_eventually(p:ℝ≥0×Ω):∀ᶠn:ℕ in atTop,raw 𝓕 Q H g n p=g p:=by
  obtain ⟨N,hN⟩:=exists_nat_ge ‖g p‖
  filter_upwards [eventually_ge_atTop N] with n hn
  exact if_pos (hN.trans (by exact_mod_cast hn))

variable(μ:Measure Ω)[IsFiniteMeasure μ]

theorem memLp(n:ℕ):@MemLp _ _ 𝓕.predictable _ _ (raw 𝓕 Q H g n) 2
    ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
  have :IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  exact MemLp.of_bound (raw_predictable 𝓕 Q H g n).aestronglyMeasurable (n:ℝ)
    (ae_of_all _ (raw_bound 𝓕 Q H g n))

/-- The identical bounded predictable function defines a process under
either finite measure, without transferring the unbounded L2 process. -/
def process(n:ℕ):Process (E:=C) 𝓕 μ H:=
  (memLp 𝓕 Q H g μ n).toLp (raw 𝓕 Q H g n)

theorem process_ae(n:ℕ):process 𝓕 Q H g μ n=ᵐ[energyMeasure μ H] raw 𝓕 Q H g n:=
  ae_eq_of_ae_eq_trim (memLp 𝓕 Q H g μ n).coeFn_toLp

theorem matched [IsFiniteMeasure Q](hQμ:Q≪μ)(n:ℕ):
    process 𝓕 Q H g μ n=ᵐ[energyMeasure Q H] process 𝓕 Q H g Q n:=by
  have hac:energyMeasure Q H≪energyMeasure μ H:=
    Measure.AbsolutelyContinuous.prod (Measure.AbsolutelyContinuous.refl _) hQμ
  exact (hac.ae_eq (process_ae 𝓕 Q H g μ n)).trans (process_ae 𝓕 Q H g Q n).symm

omit [IsFiniteMeasure μ] in
theorem raw_tendsto(p:ℝ≥0×Ω):Tendsto (fun n=>raw 𝓕 Q H g n p) atTop (𝓝 (g p)):=
  tendsto_const_nhds.congr' ((raw_eventually 𝓕 Q H g p).mono (fun _ h=>h.symm))

/-- Norm truncations converge in the actual Q-predictable L2 space.
The same truncations are bounded processes under every finite μ. -/
theorem tendsto [IsFiniteMeasure Q]:
    Tendsto (process 𝓕 Q H g Q) atTop (𝓝 g):=by
  have hi:Integrable (fun p=>‖g p‖^2) (energyMeasure Q H):=
    (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp g)).norm.integrable_sq
  apply PredictableSquareDominatedLimit.tendsto 𝓕 Q H (process 𝓕 Q H g Q) g (fun p=>‖g p‖^2) hi
  · intro n
    filter_upwards [process_ae 𝓕 Q H g Q n] with p hp
    rw [hp]
    exact pow_le_pow_left₀ (norm_nonneg _) (raw_le 𝓕 Q H g n p) 2
  · exact ae_of_all _ (fun _=>le_rfl)
  · filter_upwards [ae_all_iff.mpr (process_ae 𝓕 Q H g Q)] with p hp
    apply (raw_tendsto 𝓕 Q H g p).congr'
    exact Eventually.of_forall (fun n=>(hp n).symm)
end SHE.PredictableBoundedTruncation
