module

public import SHE.HeatPartition
public import SHE.StoppedFourier

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.GlobalHeatSpan
open MeasureTheory Finset SHE.HeatLine SHE.HeatCluster SHE.HeatCoherence SHE.HeatPartition
open scoped InnerProductSpace

def weight (t a x : ℝ) : ℝ := (Real.sqrt t)⁻¹ * Real.exp (-(x-a)^2/(4*t))

theorem weight_nonneg (t a x : ℝ) : 0 ≤ weight t a x := by unfold weight; positivity

/-- The Hilbert-space cluster estimate applied to actual square-integrable
functions and their literal line inner products. -/
theorem separated_functions_envelope {I : Type*} [Fintype I] (f : I → ℝ → ℂ) (x₀ : ℝ)
    (hf : ∀ i, MemLp (f i) 2 volume) (w : I → ℝ) {C ε : ℝ} (hC : 0 ≤ C)
    (hw : ∀ i, 0 ≤ w i)
    (hb : ∀ i, ‖f i x₀‖^2 ≤ C*(∫ x : ℝ, ‖f i x‖^2)*w i)
    (hε : 0 ≤ ε) (hsmall : ε*(Fintype.card I:ℝ) ≤ 1/2)
    (hoff : ∀ i j, i ≠ j → ‖∫ x : ℝ, star (f i x)*f j x‖ ≤
      ε*Real.sqrt (∫ x : ℝ, ‖f i x‖^2)*Real.sqrt (∫ x : ℝ, ‖f j x‖^2)) :
    ‖∑ i,f i x₀‖^2 ≤ (2*(Fintype.card I:ℝ)*C)*
      (∫ x : ℝ, ‖∑ i,f i x‖^2)*(∑ i,w i) := by
  classical
  let u (i : I) : Lp ℂ 2 (volume : Measure ℝ) := (hf i).toLp (f i)
  have hnorm (i : I) : ‖u i‖^2 = ∫ x : ℝ, ‖f i x‖^2 :=
    SHE.StoppedFourier.toLp_norm_sq_eq_integral (hf i)
  have hsqrt (i : I) : Real.sqrt (∫ x : ℝ, ‖f i x‖^2) = ‖u i‖ := by
    rw [← hnorm,Real.sqrt_sq (norm_nonneg _)]
  have hi (i j : I) : inner ℂ (u i) (u j) = ∫ x : ℝ, star (f i x)*f j x := by
    rw [SHE.StoppedFourier.toLp_inner_eq_integral (hf i) (hf j)]
    congr 1
    ext x
    exact RCLike.inner_apply' (𝕜 := ℂ) _ _
  have hsumAE : (fun x => (∑ i,u i) x) =ᵐ[volume] fun x => ∑ i,f i x := by
    filter_upwards [Lp.coeFn_finsetSum univ u,ae_all_iff.mpr (fun i => (hf i).coeFn_toLp)] with x hx hy
    rw [hx]
    simp only [Finset.sum_apply]
    exact sum_congr rfl (fun i _ => hy i)
  have hsum : ‖∑ i,u i‖^2 = ∫ x : ℝ, ‖∑ i,f i x‖^2 := by
    rw [SHE.StoppedFourier.L2_norm_sq_eq_integral]
    exact integral_congr_ae (hsumAE.mono (fun _ hx => congrArg (fun z : ℂ => ‖z‖^2) hx))
  have hh := SHE.SeparatedSums.separated_sum_envelope u (fun i => f i x₀) w hC hw
    (fun i => by rw [hnorm]; exact hb i) hε hsmall (fun i j hij => by
      rw [hi,← hsqrt,← hsqrt]
      exact hoff i j hij)
  rwa [hsum] at hh

def compactRatio (q : ℕ) (K : ℝ) : ℝ := ((max 1 K)^q)⁻¹
def compactRadius (q : ℕ) (K : ℝ) : ℝ := (q:ℝ)*max 1 K
def crossTolerance (q : ℕ) : ℝ := (2*(q:ℝ)+1)⁻¹

theorem compactRatio_pos (q : ℕ) (K : ℝ) : 0 < compactRatio q K := by
  unfold compactRatio
  exact inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _)

theorem compactRadius_nonneg (q : ℕ) (K : ℝ) : 0 ≤ compactRadius q K := by
  unfold compactRadius
  exact mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (le_max_left _ _))

theorem crossTolerance_pos (q : ℕ) : 0 < crossTolerance q := by unfold crossTolerance; positivity

def clusterConstant (q : ℕ) (K : ℝ) : ℝ := Classical.choose
  (compact_heat_cluster_envelope q (compactRatio_pos q K) (compactRadius_nonneg q K))

theorem clusterConstant_spec (q : ℕ) (K : ℝ) :
    0 < clusterConstant q K ∧ ∀ (t a : Fin q → ℝ) (T c : ℝ), 0 < T →
      (∀ i, compactRatio q K*T ≤ t i) → (∀ i,t i ≤ T) →
      (∀ i,|a i-c| ≤ compactRadius q K*Real.sqrt T) →
      ∀ f : ℂ → ℂ, f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) →
      Integrable (fun x : ℝ => ‖f (x:ℂ)‖^2) ∧ ∀ x : ℝ,
        ‖f (x:ℂ)‖^2 ≤ clusterConstant q K*(Real.sqrt T)⁻¹*
          (∫ u : ℝ,‖f (u:ℂ)‖^2)*Real.exp (-(x-c)^2/(4*T)) := Classical.choose_spec
  (compact_heat_cluster_envelope q (compactRatio_pos q K) (compactRadius_nonneg q K))

def crossThreshold (q : ℕ) (K : ℝ) : ℝ := Classical.choose
  (compact_heat_clusters_almost_orthogonal q q (compactRatio_pos q K)
    (compactRadius_nonneg q K) (crossTolerance_pos q))

theorem crossThreshold_spec (q : ℕ) (K : ℝ) :
    1 ≤ crossThreshold q K ∧
      ∀ (t a u b : Fin q → ℝ) (T U c d : ℝ), 0 < T → 0 < U →
      (∀ i,compactRatio q K*T ≤ t i) → (∀ i,t i ≤ T) →
      (∀ i,|a i-c| ≤ compactRadius q K*Real.sqrt T) →
      (∀ i,compactRatio q K*U ≤ u i) → (∀ i,u i ≤ U) →
      (∀ i,|b i-d| ≤ compactRadius q K*Real.sqrt U) →
      (T > crossThreshold q K*U ∨ U > crossThreshold q K*T ∨
        |c-d| > crossThreshold q K*Real.sqrt (max T U)) →
      ∀ f g : ℂ → ℂ,
        f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) →
        g ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (u i) (b i))) →
        Integrable (fun x : ℝ => f (x:ℂ)*star (g (x:ℂ))) ∧
          ‖∫ x : ℝ,f (x:ℂ)*star (g (x:ℂ))‖ ≤ crossTolerance q*
            Real.sqrt (∫ x : ℝ,‖f (x:ℂ)‖^2)*Real.sqrt (∫ x : ℝ,‖g (x:ℂ)‖^2) := Classical.choose_spec
  (compact_heat_clusters_almost_orthogonal q q (compactRatio_pos q K)
    (compactRadius_nonneg q K) (crossTolerance_pos q))

def clusterThresholds (q : ℕ) : ℕ → ℝ := FiniteStabilization.thresholds (crossThreshold q)

def uniformClusterConstant (q : ℕ) : ℝ :=
  1+∑ k ∈ range (q^2+1),clusterConstant q (clusterThresholds q k)

theorem uniformClusterConstant_pos (q : ℕ) : 0 < uniformClusterConstant q := by
  unfold uniformClusterConstant
  have hh := sum_nonneg (s := range (q^2+1))
    (fun k _ => (clusterConstant_spec q (clusterThresholds q k)).1.le)
  linarith

theorem clusterConstant_le_uniform (q k : ℕ) (hk : k ≤ q^2) :
    clusterConstant q (clusterThresholds q k) ≤ uniformClusterConstant q := by
  have hh := single_le_sum (s := range (q^2+1))
    (fun j _ => (clusterConstant_spec q (clusterThresholds q j)).1.le)
    (show k ∈ range (q^2+1) by simp only [mem_range]; omega)
  unfold uniformClusterConstant
  linarith

theorem separation_mono {T U c d L M : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) (hLM : L ≤ M)
    (hsep : T > M*U ∨ U > M*T ∨ |c-d| > M*Real.sqrt (max T U)) :
    T > L*U ∨ U > L*T ∨ |c-d| > L*Real.sqrt (max T U) := by
  rcases hsep with h|h|h
  · exact Or.inl ((mul_le_mul_of_nonneg_right hLM hU).trans_lt h)
  · exact Or.inr (Or.inl ((mul_le_mul_of_nonneg_right hLM hT).trans_lt h))
  · exact Or.inr (Or.inr ((mul_le_mul_of_nonneg_right hLM (Real.sqrt_nonneg _)).trans_lt h))

theorem stable_partition_envelope (q : ℕ) (t a : Fin q → ℝ) (z : Fin q → ℂ)
    (ht : ∀ i,0 < t i) {K L : ℝ} (hK : 1 ≤ K) (hKL : crossThreshold q K ≤ L)
    (hstable : ∀ i j,(graph t a K).Reachable i j ↔ (graph t a L).Reachable i j) :
    Integrable (fun x : ℝ => ‖(∑ i,z i • heatEntire (t i) (a i)) (x:ℂ)‖^2) ∧
      ∀ x : ℝ,‖(∑ i,z i • heatEntire (t i) (a i)) (x:ℂ)‖^2 ≤
        (2*(q:ℝ)*clusterConstant q K)*
          (∫ u : ℝ,‖(∑ i,z i • heatEntire (t i) (a i)) (u:ℂ)‖^2)*
          (∑ i,weight (t i) (a i) x) := by
  classical
  let G := graph t a K
  let F := clusterFunction G t a z
  let r := representative G t
  have hgeometry (C : G.ConnectedComponent) (i : Fin q) :
      compactRatio q K*t (r C) ≤ paddedAge G t C i ∧
      paddedAge G t C i ≤ t (r C) ∧
      |paddedCenter G t a C i-a (r C)| ≤ compactRadius q K*Real.sqrt (t (r C)) := by
    simpa only [compactRatio,compactRadius,max_eq_right hK,Fintype.card_fin] using
      padded_geometry t a ht hK C i
  have hspan (C : G.ConnectedComponent) : F C ∈ Submodule.span ℂ (Set.range
      (fun i => heatEntire (paddedAge G t C i) (paddedCenter G t a C i))) :=
    clusterFunction_padded_span G t a z C
  have hcluster (C : G.ConnectedComponent) := (clusterConstant_spec q K).2
    (paddedAge G t C) (paddedCenter G t a C) (t (r C)) (a (r C)) (ht (r C))
    (fun i => (hgeometry C i).1) (fun i => (hgeometry C i).2.1)
    (fun i => (hgeometry C i).2.2) (F C) (hspan C)
  have hmem (C : G.ConnectedComponent) : MemLp (fun x : ℝ => F C (x:ℂ)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm
      (continuous_heat_span _ _ _ (hspan C)).aestronglyMeasurable).mpr (hcluster C).1
  have htotal : (fun x : ℝ => ∑ C : G.ConnectedComponent,F C (x:ℂ)) =
      fun x : ℝ => (∑ i,z i • heatEntire (t i) (a i)) (x:ℂ) := by
    funext x
    simpa only [Finset.sum_apply] using congrFun (clusterFunction_sum G t a z) (x:ℂ)
  have hsumMem : MemLp (fun x : ℝ => ∑ C : G.ConnectedComponent,F C (x:ℂ)) 2 volume := by
    exact memLp_finsetSum univ (fun C _ => hmem C)
  refine ⟨?_,fun x => ?_⟩
  · rw [htotal] at hsumMem
    exact (memLp_two_iff_integrable_sq_norm hsumMem.aestronglyMeasurable).mp hsumMem
  · have hoff (C D : G.ConnectedComponent) (hCD : C ≠ D) :
        ‖∫ u : ℝ,star (F C (u:ℂ))*F D (u:ℂ)‖ ≤ crossTolerance q*
          Real.sqrt (∫ u : ℝ,‖F C (u:ℂ)‖^2)*Real.sqrt (∫ u : ℝ,‖F D (u:ℂ)‖^2) := by
      have hs := separation_mono (ht (r D)).le (ht (r C)).le hKL
        (representatives_separation t a hstable D C hCD.symm)
      have hh := ((crossThreshold_spec q K).2
        (paddedAge G t D) (paddedCenter G t a D) (paddedAge G t C) (paddedCenter G t a C)
        (t (r D)) (t (r C)) (a (r D)) (a (r C)) (ht (r D)) (ht (r C))
        (fun i => (hgeometry D i).1) (fun i => (hgeometry D i).2.1)
        (fun i => (hgeometry D i).2.2) (fun i => (hgeometry C i).1)
        (fun i => (hgeometry C i).2.1) (fun i => (hgeometry C i).2.2)
        hs (F D) (F C) (hspan D) (hspan C)).2
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hh
    have hcard : (Fintype.card G.ConnectedComponent:ℝ) ≤ (q:ℝ) := by
      exact_mod_cast (card_components_le G).trans_eq (Fintype.card_fin q)
    have hsmall : crossTolerance q*(Fintype.card G.ConnectedComponent:ℝ) ≤ 1/2 := by
      have hh := mul_le_mul_of_nonneg_left hcard (crossTolerance_pos q).le
      have hden : 0 < 2*(q:ℝ)+1 := by positivity
      have hb : crossTolerance q*(q:ℝ) ≤ 1/2 := by
        unfold crossTolerance
        rw [inv_mul_eq_div,div_le_iff₀ hden]
        linarith
      exact hh.trans hb
    have hb (C : G.ConnectedComponent) : ‖F C (x:ℂ)‖^2 ≤ clusterConstant q K*
        (∫ u : ℝ,‖F C (u:ℂ)‖^2)*weight (t (r C)) (a (r C)) x := by
      simpa only [weight,mul_comm,mul_left_comm,mul_assoc] using (hcluster C).2 x
    have hh := separated_functions_envelope (fun C u => F C (u:ℂ)) x hmem
      (fun C => weight (t (r C)) (a (r C)) x) (clusterConstant_spec q K).1.le
      (fun C => weight_nonneg _ _ _) hb (crossTolerance_pos q).le hsmall hoff
    have hpoint (u : ℝ) := congrFun htotal u
    simp_rw [hpoint] at hh
    have hw := sum_representatives_le G t (fun i => weight (t i) (a i) x)
      (fun i => weight_nonneg _ _ _)
    have hE : 0 ≤ ∫ u : ℝ,‖(∑ i,z i • heatEntire (t i) (a i)) (u:ℂ)‖^2 :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hCpos := (clusterConstant_spec q K).1
    exact hh.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num))
          (clusterConstant_spec q K).1.le) hE)
      hw (sum_nonneg (s := univ) (fun _ _ => weight_nonneg _ _ _)) (by positivity))

/-- The full real-line heat-span localization bound. Ages and centers are
arbitrary; the constant depends only on the number of observations.
All collisions and cancellations are included in the actual span. -/
theorem global_heat_span_envelope (q : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ (t a : Fin q → ℝ),(∀ i,0 < t i) →
      ∀ f : ℂ → ℂ,f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) →
        Integrable (fun x : ℝ => ‖f (x:ℂ)‖^2) ∧ ∀ x : ℝ,
          ‖f (x:ℂ)‖^2 ≤ C*(∫ u : ℝ,‖f (u:ℂ)‖^2)*(∑ i,weight (t i) (a i) x) := by
  classical
  let C := 1+2*(q:ℝ)*uniformClusterConstant q
  have hC : 0 < C := by
    dsimp only [C]
    have hu := uniformClusterConstant_pos q
    positivity
  refine ⟨C,hC,fun t a ht f hf => ?_⟩
  obtain ⟨z,hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨k,hk,hK,_,hKL,hstable⟩ := controlled_stable_threshold t a (fun i => (ht i).le)
    (crossThreshold q)
  have hkq : k ≤ q^2 := by simpa only [Fintype.card_fin] using hk
  obtain ⟨hi,hb⟩ := stable_partition_envelope q t a z ht hK hKL hstable
  rw [hz] at hi hb
  refine ⟨hi,fun x => (hb x).trans ?_⟩
  have hcoef : 2*(q:ℝ)*clusterConstant q (FiniteStabilization.thresholds (crossThreshold q) k) ≤ C := by
    have hh := mul_le_mul_of_nonneg_left (clusterConstant_le_uniform q k hkq)
      (show 0 ≤ 2*(q:ℝ) by positivity)
    dsimp only [C]
    exact hh.trans (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (integral_nonneg (fun _ => sq_nonneg _)))
    (sum_nonneg (s := univ) (fun _ _ => weight_nonneg _ _ _))

end SHE.GlobalHeatSpan
