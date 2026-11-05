module

public import SHE.SignedPrefix

@[expose] public section
set_option autoImplicit false

/-! A coherent countable physical weighted-Haar family. A finite binary
path names a dyadic interval; its Haar input appears at every later
resolution with exactly the same name. -/

namespace SHE.FiniteHaar

open Finset Matrix MeasureTheory AddCircle CircleHeat
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev HaarNode := Option (List Bool)

def detailPath : (n : ℕ) → DetailIndex n → List Bool
  | 0, i => nomatch i
  | _ + 1, Sum.inl _ => []
  | n + 1, Sum.inr (Sum.inl i) => false :: detailPath n i
  | n + 1, Sum.inr (Sum.inr i) => true :: detailPath n i

def modePath (n : ℕ) : Option (DetailIndex n) → HaarNode := Option.map (detailPath n)

def nodeDepth : HaarNode → ℕ
  | none => 0
  | some p => p.length + 1

theorem detailPath_length (n : ℕ) (i : DetailIndex n) : (detailPath n i).length < n := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i)
    · simp [detailPath]
    · simpa only [detailPath, List.length_cons, Nat.add_lt_add_iff_right] using ih i
    · simpa only [detailPath, List.length_cons, Nat.add_lt_add_iff_right] using ih i

theorem detailPath_injective (n : ℕ) : Function.Injective (detailPath n) := by
  induction n with
  | zero => intro i; exact Empty.elim i
  | succ n ih =>
    intro i j h
    rcases i with ⟨⟩ | (i | i) <;> rcases j with ⟨⟩ | (j | j)
    all_goals simp only [detailPath] at h
    all_goals try { simp at h }
    · rfl
    · have he := ih (List.cons.inj h).2
      subst j
      rfl
    · have he := ih (List.cons.inj h).2
      subst j
      rfl

theorem modePath_injective (n : ℕ) : Function.Injective (modePath n) :=
  Option.map_injective (detailPath_injective n)

theorem modePath_depth (n : ℕ) (i : Option (DetailIndex n)) : nodeDepth (modePath n i) ≤ n := by
  cases i with
  | none => simp [modePath, nodeDepth]
  | some i => exact detailPath_length n i

theorem detailPath_surjective_below (n : ℕ) (p : List Bool) (hp : p.length < n) :
    ∃ i : DetailIndex n, detailPath n i = p := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    cases p with
    | nil => exact ⟨Sum.inl (), rfl⟩
    | cons b p =>
      obtain ⟨i, hi⟩ := ih p (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hp)
      cases b
      · exact ⟨Sum.inr (Sum.inl i), congrArg (List.cons false) hi⟩
      · exact ⟨Sum.inr (Sum.inr i), congrArg (List.cons true) hi⟩

theorem modePath_surjective_below (n : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n) :
    ∃ i : Option (DetailIndex n), modePath n i = q := by
  cases q with
  | none => exact ⟨none, rfl⟩
  | some p =>
    obtain ⟨i, hi⟩ := detailPath_surjective_below n p hq
    exact ⟨some i, congrArg some hi⟩

noncomputable def nodeMode (n : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n) : Option (DetailIndex n) :=
  (modePath_surjective_below n q hq).choose

@[simp] theorem modePath_nodeMode (n : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n) :
    modePath n (nodeMode n q hq) = q := (modePath_surjective_below n q hq).choose_spec

theorem nodeMode_injective (n : ℕ) :
    Function.Injective (fun q : {q : HaarNode // nodeDepth q ≤ n} => nodeMode n q.1 q.2) := by
  intro q r h
  apply Subtype.ext
  have he := congrArg (modePath n) h
  simpa only [modePath_nodeMode] using he

@[simp] theorem detailPath_embed (n : ℕ) (i : DetailIndex n) :
    detailPath (n + 1) (detailEmbed n i) = detailPath n i := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i)
    · rfl
    · exact congrArg (List.cons false) (ih i)
    · exact congrArg (List.cons true) (ih i)

@[simp] theorem modePath_embed (n : ℕ) (i : Option (DetailIndex n)) :
    modePath (n + 1) (modeEmbed n i) = modePath n i := by
  cases i <;> simp [modePath, modeEmbed]

@[simp] theorem modePath_lift (n r : ℕ) (i : Option (DetailIndex n)) :
    modePath (n + r) (modeLift n r i) = modePath n i := by
  induction r with
  | zero => rfl
  | succ r ih => exact (modePath_embed (n + r) _).trans ih

/-- A fixed physical weighted-Haar column for every actual dyadic input
node, defined at its first resolution and independent of later grids. -/
noncomputable def globalHaarColumn (q : HaarNode) (f : CircleL2) : CircleL2 :=
  fixedHaarColumn (nodeDepth q) (nodeMode (nodeDepth q) q le_rfl) f

theorem globalHaarColumn_tendsto (q : HaarNode) (f : ℕ → CircleL2) (g : CircleL2)
    (m U : ℝ) (hm : 0 < m)
    (hf : ∀ N, ∀ᵐ y ∂haarAddCircle, m ≤ (f N y).re ∧ (f N y).re ≤ U)
    (hfg : Filter.Tendsto f Filter.atTop (nhds g)) :
    Filter.Tendsto (fun N => globalHaarColumn q (f N)) Filter.atTop (nhds (globalHaarColumn q g)) :=
  fixedHaarColumn_tendsto_of_uniform_elliptic _ _ f g m U hm hf hfg

theorem nodeMode_lift (n r : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n)
    (hqr : nodeDepth q ≤ n + r) :
    nodeMode (n + r) q hqr = modeLift n r (nodeMode n q hq) := by
  apply modePath_injective (n + r)
  simp

/-- The coherent countable column is literally the finite physical column
at every resolution containing its node. -/
theorem globalHaarColumn_gridStep (n : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n)
    (a : Grid n → ℝ) (ha : ∀ x, 0 < a x) :
    globalHaarColumn q (gridStep n a) =
      gridStep n (fun y => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * localFactor n a y (nodeMode n q hq)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [globalHaarColumn, fixedHaarColumn_ancestor_gridStep _ r _ a ha]
  rw [nodeMode_lift (nodeDepth q) r q le_rfl hq]

theorem signedColumn_global (n : ℕ) (q : HaarNode) (hq : nodeDepth q ≤ n)
    (c d : Grid n → ℝ) (hc : ∀ x, 0 < c x) (hd : ∀ x, 0 < d x) :
    signedColumn n c d (nodeMode n q hq) =
      globalHaarColumn q (gridStep n c) - globalHaarColumn q (gridStep n d) := by
  rw [signedColumn_fixedHaar, fixedHaarColumn_gridStep, fixedHaarColumn_gridStep,
    globalHaarColumn_gridStep n q hq c hc, globalHaarColumn_gridStep n q hq d hd]

theorem gridStep_bounds_ae (n : ℕ) (a : Grid n → ℝ) (m U : ℝ)
    (ha : ∀ x, m ≤ a x ∧ a x ≤ U) :
    ∀ᵐ y ∂haarAddCircle, m ≤ (gridStep n a y).re ∧ (gridStep n a y).re ≤ U := by
  filter_upwards [gridStep_ae_cellIndex n a] with y hy
  simpa [hy] using ha ((gridCellEquiv n).symm (cellIndex n y))

theorem continuousAt_globalHaarColumn (q : HaarNode) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    ContinuousAt (globalHaarColumn q) f := by
  exact continuousAt_fixedHaarColumn _ _ f
    (fun x => hm.trans_le (localAverage_bounds_ae _ f m U hf x).1)

noncomputable def globalSignedColumn (q : HaarNode) (f g : CircleL2) : CircleL2 :=
  globalHaarColumn q f - globalHaarColumn q g

noncomputable def finiteNodeColumn (n : ℕ) (c d : Grid n → ℝ) (t : ℝ) (q : HaarNode) : CircleL2 :=
  if hq : nodeDepth q ≤ n then heat t (signedColumn n c d (nodeMode n q hq)) else 0

theorem finiteNodeColumn_tendsto (t : ℝ) (q : HaarNode)
    (c d : ∀ N, Grid N → ℝ) (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ N x, m ≤ c N x ∧ c N x ≤ U) (hd : ∀ N x, m ≤ d N x ∧ d N x ≤ U)
    (hcf : Filter.Tendsto (fun N => gridStep N (c N)) Filter.atTop (nhds f))
    (hdg : Filter.Tendsto (fun N => gridStep N (d N)) Filter.atTop (nhds g)) :
    Filter.Tendsto (fun N => finiteNodeColumn N (c N) (d N) t q) Filter.atTop
      (nhds (heat t (globalSignedColumn q f g))) := by
  have hc' := globalHaarColumn_tendsto q (fun N => gridStep N (c N)) f m U hm
    (fun N => gridStep_bounds_ae N (c N) m U (hc N)) hcf
  have hd' := globalHaarColumn_tendsto q (fun N => gridStep N (d N)) g m U hm
    (fun N => gridStep_bounds_ae N (d N) m U (hd N)) hdg
  have hlim := (heat t).continuous.tendsto (globalSignedColumn q f g) |>.comp (hc'.sub hd')
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (nodeDepth q)] with N hN
  rw [finiteNodeColumn, dite_eq_left hN, signedColumn_global N q hN (c N) (d N)
    (fun x => hm.trans_le (hc N x).1) (fun x => hm.trans_le (hd N x).1)]
  rfl

theorem finiteNodeColumn_sum_le (n : ℕ) (c d : Grid n → ℝ) (t : ℝ) (s : Finset HaarNode) :
    (∑ q ∈ s, ‖finiteNodeColumn n c d t q‖ ^ 2) ≤
      ∑ j : Option (DetailIndex n), ‖heat t (signedColumn n c d j)‖ ^ 2 := by
  classical
  let a : HaarNode → ℝ := fun q => ‖finiteNodeColumn n c d t q‖ ^ 2
  let h := s.filter (fun q => nodeDepth q ≤ n)
  have he : (∑ q ∈ s, a q) = ∑ q ∈ h, a q := by
    symm
    apply sum_subset (filter_subset _ _)
    intro q hq hnot
    have hn : ¬ nodeDepth q ≤ n := by simpa only [mem_filter, hq, true_and] using hnot
    simp [a, finiteNodeColumn, hn]
  rw [show (∑ q ∈ s, ‖finiteNodeColumn n c d t q‖ ^ 2) = ∑ q ∈ h, a q from he]
  let e : HaarNode → Option (DetailIndex n) := fun q =>
    if hq : nodeDepth q ≤ n then nodeMode n q hq else none
  have hinj : Set.InjOn e (↑h : Set HaarNode) := by
    intro q hq r hr heq
    have hq' := (mem_filter.mp hq).2
    have hr' := (mem_filter.mp hr).2
    have he' := congrArg (modePath n) heq
    simpa only [e, dite_eq_left hq', dite_eq_left hr', modePath_nodeMode] using he'
  calc
    _ = ∑ q ∈ h, ‖heat t (signedColumn n c d (e q))‖ ^ 2 := by
      apply sum_congr rfl
      intro q hq
      simp only [a, finiteNodeColumn, e, dite_eq_left (mem_filter.mp hq).2]
    _ = ∑ j ∈ h.image e, ‖heat t (signedColumn n c d j)‖ ^ 2 := by
      rw [sum_image]
      exact hinj
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- The full countable signed physical heat-Haar estimate. Its inputs are
only genuine uniformly elliptic coefficient approximations converging in
circle `L²`. The countable input family, its finite-grid identification,
and every column limit are constructed above. -/
theorem global_signed_heat_of_grid_approximation {t κ Λ ρ : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (c d : ∀ N, Grid N → ℝ) (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ N x, m ≤ c N x ∧ c N x ≤ U) (hd : ∀ N x, m ≤ d N x ∧ d N x ≤ U)
    (hcf : Filter.Tendsto (fun N => gridStep N (c N)) Filter.atTop (nhds f))
    (hdg : Filter.Tendsto (fun N => gridStep N (d N)) Filter.atTop (nhds g)) :
    Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f - g) *
          (Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ)) := by
  let T := Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ)
  let B : ℕ → ℝ := fun N => signedHeatSqConstant κ ρ m U *
    StepInput.negativeEnergy κ Λ ρ (gridStep N (c N - d N)) * T
  have hdiff : Filter.Tendsto (fun N => gridStep N (c N - d N)) Filter.atTop (nhds (f - g)) := by
    simpa only [gridStep_sub] using hcf.sub hdg
  have hB : Filter.Tendsto B Filter.atTop
      (nhds (signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f - g) * T)) :=
    (((continuous_negativeEnergy hΛ hρ.le).tendsto (f - g)).comp hdiff).const_mul _ |>.mul_const T
  have hfinite (s : Finset HaarNode) :
      (∑ q ∈ s, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f - g) * T := by
    have hlim : Filter.Tendsto (fun N => ∑ q ∈ s, ‖finiteNodeColumn N (c N) (d N) t q‖ ^ 2)
        Filter.atTop (nhds (∑ q ∈ s, ‖heat t (globalSignedColumn q f g)‖ ^ 2)) :=
      tendsto_finsetSum s (fun q _ => (finiteNodeColumn_tendsto t q c d f g m U hm hc hd hcf hdg).norm.pow 2)
    apply le_of_tendsto_of_tendsto hlim hB
    apply Filter.Eventually.of_forall
    intro N
    exact (finiteNodeColumn_sum_le N (c N) (d N) t s).trans
      (signed_heat_finite_HS_sq ht ht1 hκ hΛ hρ hρhalf N (c N) (d N) m U hm (hc N) (hd N))
  have hs : Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs, Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite⟩

theorem global_signed_heat_tail_of_grid_approximation {t κ Λ ρ : ℝ}
    (ht : 1 ≤ t) (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (c d : ∀ N, Grid N → ℝ) (f g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ N x, m ≤ c N x ∧ c N x ≤ U) (hd : ∀ N x, m ≤ d N x ∧ d N x ≤ U)
    (hcf : Filter.Tendsto (fun N => gridStep N (c N)) Filter.atTop (nhds f))
    (hdg : Filter.Tendsto (fun N => gridStep N (d N)) Filter.atTop (nhds g)) :
    Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) ∧
      (∑' q : HaarNode, ‖heat t (globalSignedColumn q f g)‖ ^ 2) ≤
        signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (f - g) * (Λ ^ ρ + 1) := by
  have hone := global_signed_heat_of_grid_approximation (by norm_num : (0 : ℝ) < 1) le_rfl
    hκ hΛ hρ hρhalf c d f g m U hm hc hd hcf hdg
  have hs : Summable (fun q : HaarNode => ‖heat t (globalSignedColumn q f g)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun q => heat_sq_le_at_one ht _) hone.1
  refine ⟨hs, (hs.tsum_le_tsum (fun q => heat_sq_le_at_one ht _) hone.1).trans ?_⟩
  simpa only [Real.one_rpow, mul_one] using hone.2

end SHE.FiniteHaar
