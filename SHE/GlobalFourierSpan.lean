module

public import SHE.FourierParseval

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.GlobalFourierSpan
open MeasureTheory Finset SHE.HeatLine SHE.HeatCluster SHE.HeatCoherence SHE.HeatPartition
open SHE.GlobalHeatSpan SHE.FourierCluster SHE.FourierHeatLine SHE.FourierParseval
open scoped InnerProductSpace FourierTransform

def frequencyWeight (r t ξ : ℝ) : ℝ := Real.sqrt t*Real.exp (-r*t*ξ^2)
theorem frequencyWeight_nonneg (r t ξ : ℝ) : 0 ≤ frequencyWeight r t ξ := by
  unfold frequencyWeight
  positivity

def clusterCoefficients {I : Type*} [Fintype I] (G : SimpleGraph I) (z : I → ℂ)
    (C : G.ConnectedComponent) (i : I) : ℂ := by
  classical
  exact if i ∈ vertices G C then z i else 0

theorem physicalCluster_eq {q : ℕ} (G : SimpleGraph (Fin q)) (t a : Fin q → ℝ)
    (z : Fin q → ℂ) (C : G.ConnectedComponent) (x : ℝ) :
    physicalSum t a (clusterCoefficients G z C) x = clusterFunction G t a z C (x:ℂ) := by
  classical
  simp only [physicalSum,clusterCoefficients,ite_mul,zero_mul,← sum_filter]
  have he : univ.filter (fun i => i ∈ vertices G C) = vertices G C := by ext i; simp
  rw [he]
  simp only [clusterFunction,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem frequencyCluster_eq {q : ℕ} (G : SimpleGraph (Fin q)) (t a : Fin q → ℝ)
    (z : Fin q → ℂ) (C : G.ConnectedComponent) (ξ : ℝ) :
    frequencySum t a (clusterCoefficients G z C) ξ =
      ∑ i ∈ vertices G C,z i*(heatMass (t i):ℂ)*frequencyGaussian (t i) (a i) (ξ:ℂ) := by
  classical
  simp only [frequencySum,clusterCoefficients,ite_mul,zero_mul,← sum_filter]
  have he : univ.filter (fun i => i ∈ vertices G C) = vertices G C := by ext i; simp
  rw [he]

theorem frequencyCluster_padded_span {q : ℕ} (G : SimpleGraph (Fin q))
    (t a : Fin q → ℝ) (z : Fin q → ℂ) (C : G.ConnectedComponent) :
    (∑ i ∈ vertices G C,(z i*(heatMass (t i):ℂ)) • frequencyGaussian (t i) (a i)) ∈
      Submodule.span ℂ (Set.range (fun i => frequencyGaussian (paddedAge G t C i) (paddedCenter G t a C i))) := by
  classical
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun i => if i ∈ vertices G C then z i*(heatMass (t i):ℂ) else 0,?_⟩
  simp only [ite_smul,zero_smul]
  rw [← sum_filter]
  have he : univ.filter (fun i => i ∈ vertices G C) = vertices G C := by ext i; simp
  rw [he]
  apply sum_congr rfl
  intro i hi
  simp [paddedAge,paddedCenter,hi]

theorem frequencyCluster_sum {q : ℕ} (G : SimpleGraph (Fin q)) (t a : Fin q → ℝ)
    (z : Fin q → ℂ) (ξ : ℝ) :
    (∑ C : G.ConnectedComponent,frequencySum t a (clusterCoefficients G z C) ξ) = frequencySum t a z ξ := by
  simp_rw [frequencyCluster_eq]
  exact sum_components G _

/-- Hilbert energy controls arbitrary observed values attached to the
same actual square-integrable cluster functions. -/
theorem separated_values_envelope {I : Type*} [Fintype I] (f : I → ℝ → ℂ)
    (hf : ∀ i,MemLp (f i) 2 volume) (v : I → ℂ) (w : I → ℝ) {C ε : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i,0 ≤ w i)
    (hb : ∀ i,‖v i‖^2 ≤ C*(∫ x : ℝ,‖f i x‖^2)*w i)
    (hε : 0 ≤ ε) (hsmall : ε*(Fintype.card I:ℝ) ≤ 1/2)
    (hoff : ∀ i j,i≠j → ‖∫ x : ℝ,star (f i x)*f j x‖ ≤
      ε*Real.sqrt (∫ x : ℝ,‖f i x‖^2)*Real.sqrt (∫ x : ℝ,‖f j x‖^2)) :
    ‖∑ i,v i‖^2 ≤ (2*(Fintype.card I:ℝ)*C)*(∫ x : ℝ,‖∑ i,f i x‖^2)*(∑ i,w i) := by
  classical
  let u (i : I) : Lp ℂ 2 (volume : Measure ℝ) := (hf i).toLp (f i)
  have hn (i : I) : ‖u i‖^2 = ∫ x : ℝ,‖f i x‖^2 := SHE.StoppedFourier.toLp_norm_sq_eq_integral (hf i)
  have hsqrt (i : I) : Real.sqrt (∫ x : ℝ,‖f i x‖^2) = ‖u i‖ := by rw [← hn,Real.sqrt_sq (norm_nonneg _)]
  have hi (i j : I) : inner ℂ (u i) (u j) = ∫ x : ℝ,star (f i x)*f j x := by
    rw [SHE.StoppedFourier.toLp_inner_eq_integral (hf i) (hf j)]
    congr 1
    ext x
    exact RCLike.inner_apply' (𝕜:=ℂ) _ _
  have hAE : (fun x => (∑ i,u i) x) =ᵐ[volume] fun x => ∑ i,f i x := by
    filter_upwards [Lp.coeFn_fun_finsetSum univ u,ae_all_iff.mpr (fun i => (hf i).coeFn_toLp)] with x hx hy
    rw [hx]
    exact sum_congr rfl (fun i _ => hy i)
  have hsum : ‖∑ i,u i‖^2 = ∫ x : ℝ,‖∑ i,f i x‖^2 := by
    rw [SHE.StoppedFourier.L2_norm_sq_eq_integral]
    exact integral_congr_ae (hAE.mono (fun _ hx => congrArg (fun z : ℂ => ‖z‖^2) hx))
  have hh := SHE.SeparatedSums.separated_sum_envelope u v w hC hw
    (fun i => by rw [hn];exact hb i) hε hsmall (fun i j hij => by rw [hi,← hsqrt,← hsqrt];exact hoff i j hij)
  rwa [hsum] at hh

def fourierConstant (q : ℕ) (K : ℝ) : ℝ := Classical.choose
  (compact_fourier_cluster_envelope q (compactRatio_pos q K) (compactRadius_nonneg q K))

theorem fourierConstant_spec (q : ℕ) (K : ℝ) :
    0 < fourierConstant q K ∧ ∀ (t a : Fin q → ℝ) (T c : ℝ),0 < T →
      (∀ i,compactRatio q K*T ≤ t i) → (∀ i,t i ≤ T) →
      (∀ i,|a i-c| ≤ compactRadius q K*Real.sqrt T) →
      ∀ f : ℂ → ℂ,f ∈ Submodule.span ℂ (Set.range (fun i => frequencyGaussian (t i) (a i))) →
      Integrable (fun ξ : ℝ => ‖f (ξ:ℂ)‖^2) ∧ ∀ ξ : ℝ,
        ‖f (ξ:ℂ)‖^2 ≤ fourierConstant q K*Real.sqrt T*(∫ u : ℝ,‖f (u:ℂ)‖^2)*
          Real.exp (-(4*Real.pi^2*compactRatio q K)*T*ξ^2) :=
  Classical.choose_spec (compact_fourier_cluster_envelope q (compactRatio_pos q K) (compactRadius_nonneg q K))

def uniformFourierConstant (q : ℕ) : ℝ :=
  1+∑ k ∈ range (q^2+1),fourierConstant q (clusterThresholds q k)

theorem uniformFourierConstant_pos (q : ℕ) : 0 < uniformFourierConstant q := by
  unfold uniformFourierConstant
  have hh := sum_nonneg (s := range (q^2+1))
    (fun k _ => (fourierConstant_spec q (clusterThresholds q k)).1.le)
  linarith

theorem fourierConstant_le_uniform (q k : ℕ) (hk : k ≤ q^2) :
    fourierConstant q (clusterThresholds q k) ≤ uniformFourierConstant q := by
  have hh := single_le_sum (s := range (q^2+1))
    (fun j _ => (fourierConstant_spec q (clusterThresholds q j)).1.le)
    (show k ∈ range (q^2+1) by simp only [mem_range];omega)
  unfold uniformFourierConstant
  linarith

def uniformFrequencyRate (q : ℕ) : ℝ := 4*Real.pi^2*((clusterThresholds q (q^2+1))^q)⁻¹

theorem uniformFrequencyRate_pos (q : ℕ) : 0 < uniformFrequencyRate q := by
  have hK := FiniteStabilization.thresholds_ge_one (crossThreshold q) (q^2+1)
  unfold uniformFrequencyRate clusterThresholds
  exact mul_pos (by positivity) (inv_pos.mpr (pow_pos (zero_lt_one.trans_le hK) _))

theorem uniformFrequencyRate_le (q k : ℕ) (hk : k ≤ q^2) :
    uniformFrequencyRate q ≤ 4*Real.pi^2*compactRatio q (clusterThresholds q k) := by
  have hK := FiniteStabilization.thresholds_ge_one (crossThreshold q) k
  have hKL := (FiniteStabilization.thresholds_strictMono (crossThreshold q)).monotone
    (show k ≤ q^2+1 by omega)
  have hp := pow_le_pow_left₀ (zero_le_one.trans hK) hKL q
  have hi := one_div_le_one_div_of_le (pow_pos (zero_lt_one.trans_le hK) q) hp
  unfold uniformFrequencyRate compactRatio
  dsimp only [clusterThresholds]
  rw [max_eq_right hK]
  simpa only [one_div] using mul_le_mul_of_nonneg_left hi (show 0 ≤ 4*Real.pi^2 by positivity)

theorem stable_partition_fourier_envelope (q k : ℕ) (hk : k ≤ q^2)
    (t a : Fin q → ℝ) (z : Fin q → ℂ) (ht : ∀ i,0 < t i) {L : ℝ}
    (hKL : crossThreshold q (clusterThresholds q k) ≤ L)
    (hstable : ∀ i j,(graph t a (clusterThresholds q k)).Reachable i j ↔ (graph t a L).Reachable i j) :
    ∀ ξ : ℝ,‖frequencySum t a z ξ‖^2 ≤
      (2*(q:ℝ)*fourierConstant q (clusterThresholds q k))*(∫ x : ℝ,‖physicalSum t a z x‖^2)*
        (∑ i,frequencyWeight (uniformFrequencyRate q) (t i) ξ) := by
  classical
  let K := clusterThresholds q k
  let G := graph t a K
  let r := representative G t
  let F := clusterFunction G t a z
  let Z := clusterCoefficients G z
  let H (C : G.ConnectedComponent) : ℂ → ℂ :=
    ∑ i ∈ vertices G C,(z i*(heatMass (t i):ℂ)) • frequencyGaussian (t i) (a i)
  have hK : 1 ≤ K := FiniteStabilization.thresholds_ge_one (crossThreshold q) k
  have hgeometry (C : G.ConnectedComponent) (i : Fin q) :
      compactRatio q K*t (r C) ≤ paddedAge G t C i ∧
      paddedAge G t C i ≤ t (r C) ∧
      |paddedCenter G t a C i-a (r C)| ≤ compactRadius q K*Real.sqrt (t (r C)) := by
    simpa only [compactRatio,compactRadius,max_eq_right hK,Fintype.card_fin] using padded_geometry t a ht hK C i
  have hFspan (C : G.ConnectedComponent) := clusterFunction_padded_span G t a z C
  have hHspan (C : G.ConnectedComponent) := frequencyCluster_padded_span G t a z C
  have hmem (C : G.ConnectedComponent) : MemLp (fun x : ℝ => F C (x:ℂ)) 2 volume := by
    have hh := memLp_physicalSum t a (Z C) ht
    have he : physicalSum t a (Z C) = fun x : ℝ => F C (x:ℂ) := by
      funext x
      exact physicalCluster_eq G t a z C x
    rwa [he] at hh
  have hH (C : G.ConnectedComponent) (ξ : ℝ) : H C (ξ:ℂ) = frequencySum t a (Z C) ξ := by
    dsimp only [Z]
    rw [frequencyCluster_eq]
    simp only [H,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have henergy (C : G.ConnectedComponent) :
      (∫ ξ : ℝ,‖H C (ξ:ℂ)‖^2) = ∫ x : ℝ,‖F C (x:ℂ)‖^2 := by
    simp_rw [hH]
    rw [heat_sum_energy_eq t a (Z C) ht]
    congr 1
    funext x
    rw [physicalCluster_eq]
  have hoff (C D : G.ConnectedComponent) (hCD : C ≠ D) :
      ‖∫ x : ℝ,star (F C (x:ℂ))*F D (x:ℂ)‖ ≤ crossTolerance q*
        Real.sqrt (∫ x : ℝ,‖F C (x:ℂ)‖^2)*Real.sqrt (∫ x : ℝ,‖F D (x:ℂ)‖^2) := by
    have hs := separation_mono (ht (r D)).le (ht (r C)).le hKL
      (representatives_separation t a hstable D C hCD.symm)
    have hh := ((crossThreshold_spec q K).2
      (paddedAge G t D) (paddedCenter G t a D) (paddedAge G t C) (paddedCenter G t a C)
      (t (r D)) (t (r C)) (a (r D)) (a (r C)) (ht (r D)) (ht (r C))
      (fun i => (hgeometry D i).1) (fun i => (hgeometry D i).2.1) (fun i => (hgeometry D i).2.2)
      (fun i => (hgeometry C i).1) (fun i => (hgeometry C i).2.1) (fun i => (hgeometry C i).2.2)
      hs (F D) (F C) (hFspan D) (hFspan C)).2
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hh
  have hcard : (Fintype.card G.ConnectedComponent:ℝ) ≤ (q:ℝ) := by
    exact_mod_cast (card_components_le G).trans_eq (Fintype.card_fin q)
  have hsmall : crossTolerance q*(Fintype.card G.ConnectedComponent:ℝ) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hcard (crossTolerance_pos q).le
    have hb : crossTolerance q*(q:ℝ) ≤ 1/2 := by
      unfold crossTolerance
      rw [inv_mul_eq_div,div_le_iff₀ (show 0 < 2*(q:ℝ)+1 by positivity)]
      linarith
    exact hh.trans hb
  have htotal (x : ℝ) : (∑ C : G.ConnectedComponent,F C (x:ℂ)) = physicalSum t a z x := by
    simpa only [physicalSum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun (clusterFunction_sum G t a z) (x:ℂ)
  intro ξ
  have hbound (C : G.ConnectedComponent) : ‖frequencySum t a (Z C) ξ‖^2 ≤ fourierConstant q K*
      (∫ x : ℝ,‖F C (x:ℂ)‖^2)*frequencyWeight (uniformFrequencyRate q) (t (r C)) ξ := by
    have hh := ((fourierConstant_spec q K).2
      (paddedAge G t C) (paddedCenter G t a C) (t (r C)) (a (r C)) (ht (r C))
      (fun i => (hgeometry C i).1) (fun i => (hgeometry C i).2.1) (fun i => (hgeometry C i).2.2)
      (H C) (hHspan C)).2 ξ
    rw [hH,henergy] at hh
    have he : Real.exp (-(4*Real.pi^2*compactRatio q K)*t (r C)*ξ^2) ≤
        Real.exp (-uniformFrequencyRate q*t (r C)*ξ^2) := by
      apply Real.exp_le_exp.mpr
      have hp := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (uniformFrequencyRate_le q k hk) (ht (r C)).le) (sq_nonneg ξ)
      linarith
    have hCpos := (fourierConstant_spec q K).1
    have hE : 0 ≤ ∫ x : ℝ,‖F C (x:ℂ)‖^2 := integral_nonneg (fun _ => sq_nonneg _)
    have hle := hh.trans (mul_le_mul_of_nonneg_left he (by positivity))
    simpa only [frequencyWeight,mul_comm,mul_left_comm,mul_assoc] using hle
  have hh := separated_values_envelope (fun C x => F C (x:ℂ)) hmem
    (fun C => frequencySum t a (Z C) ξ) (fun C => frequencyWeight (uniformFrequencyRate q) (t (r C)) ξ)
    (fourierConstant_spec q K).1.le (fun _ => frequencyWeight_nonneg _ _ _) hbound
    (crossTolerance_pos q).le hsmall hoff
  dsimp only [Z] at hh
  rw [frequencyCluster_sum] at hh
  simp_rw [htotal] at hh
  have hw := sum_representatives_le G t (fun i => frequencyWeight (uniformFrequencyRate q) (t i) ξ)
    (fun _ => frequencyWeight_nonneg _ _ _)
  have hE : 0 ≤ ∫ x : ℝ,‖physicalSum t a z x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hCpos := (fourierConstant_spec q K).1
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by norm_num)) hCpos.le) hE)
    hw (sum_nonneg (s := univ) (fun _ _ => frequencyWeight_nonneg _ _ _)) (by positivity))

/-- Global frequency localization of the actual Fourier transform of a
physical heat combination. Both constants depend only on its finite order;
there is no age, center, coefficient or separation restriction. -/
theorem global_heat_fourier_envelope (q : ℕ) :
    ∃ C r : ℝ,0 < C ∧ 0 < r ∧ ∀ (t a : Fin q → ℝ) (z : Fin q → ℂ),
      (∀ i,0 < t i) → ∀ ξ : ℝ,
        ‖frequencySum t a z ξ‖^2 ≤ C*(∫ x : ℝ,‖physicalSum t a z x‖^2)*
          (∑ i,frequencyWeight r (t i) ξ) := by
  classical
  let C := 1+2*(q:ℝ)*uniformFourierConstant q
  have hC : 0 < C := by
    dsimp only [C]
    have hh := uniformFourierConstant_pos q
    positivity
  refine ⟨C,uniformFrequencyRate q,hC,uniformFrequencyRate_pos q,fun t a z ht ξ => ?_⟩
  obtain ⟨k,hk,_,_,hKL,hstable⟩ := controlled_stable_threshold t a (fun i => (ht i).le) (crossThreshold q)
  have hkq : k ≤ q^2 := by simpa only [Fintype.card_fin] using hk
  have hh := stable_partition_fourier_envelope q k hkq t a z ht hKL hstable ξ
  have hcoef : 2*(q:ℝ)*fourierConstant q (clusterThresholds q k) ≤ C := by
    have hh := mul_le_mul_of_nonneg_left (fourierConstant_le_uniform q k hkq)
      (show 0 ≤ 2*(q:ℝ) by positivity)
    dsimp only [C]
    exact hh.trans (by linarith)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (integral_nonneg (fun _ => sq_nonneg _)))
    (sum_nonneg (s := univ) (fun _ _ => frequencyWeight_nonneg _ _ _)))

theorem global_heat_span_fourier_envelope (q : ℕ) :
    ∃ C r : ℝ,0 < C ∧ 0 < r ∧ ∀ (t a : Fin q → ℝ),(∀ i,0 < t i) →
      ∀ f : ℂ → ℂ,f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) →
        ∀ ξ : ℝ,‖𝓕 (fun x : ℝ => f (x:ℂ)) ξ‖^2 ≤
          C*(∫ x : ℝ,‖f (x:ℂ)‖^2)*(∑ i,frequencyWeight r (t i) ξ) := by
  obtain ⟨C,r,hC,hr,hb⟩ := global_heat_fourier_envelope q
  refine ⟨C,r,hC,hr,fun t a ht f hf ξ => ?_⟩
  obtain ⟨z,hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  have he : (fun x : ℝ => f (x:ℂ)) = physicalSum t a z := by
    funext x
    simpa only [physicalSum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using (congrFun hz (x:ℂ)).symm
  have hE : (∫ x : ℝ,‖f (x:ℂ)‖^2) = ∫ x : ℝ,‖physicalSum t a z x‖^2 := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => congrArg (fun v : ℂ => ‖v‖^2) (congrFun he x))
  rw [he,fourier_physicalSum t a z ht,hE]
  exact hb t a z ht ξ

end SHE.GlobalFourierSpan
