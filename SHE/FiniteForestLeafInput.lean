module

public import SHE.ForestLeafInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteForestLeafInput
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2 OrderedHeatForests
open scoped BigOperators
local instance finiteForestLeafInput_periodPos : Fact (0<2*π) := ⟨by positivity⟩

theorem normTwo_finset_sum {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset ι) (f : ι→X→ℝ) (hf : ∀ i∈s,MemLp (f i) 2 μ) :
    normTwo μ (fun x=>∑ i∈s,f i x)≤∑ i∈s,normTwo μ (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _;simp [normTwo]
  | @insert i s hi ih =>
    intro hf
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs := fun j hj=>hf j (Finset.mem_insert_of_mem hj)
    have hh := normTwo_add hfi (memLp_finsetSum s hfs)
    simp only [Finset.sum_insert hi]
    exact hh.trans (add_le_add le_rfl (ih hfs))

theorem parent_leaf_memLp {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle)
    (j : Fin (m+k)) (f : HeatCircle→ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0≤B) (hfb : ∀ x,|f x|≤B) :
    MemLp (fun x=>∫ w : Fin k→HeatCircle,
      parentDensity κ hκ k t ht (values aRoot k w)*|f (x+values aRoot k w j)|
        ∂Measure.pi (fun _=>haarAddCircle)) 2 haarAddCircle := by
  let K := fun w : Fin k→HeatCircle=>parentDensity κ hκ k t ht (values aRoot k w)
  have hKc : Continuous K :=
    (ForestedScoreInput.parentDensity_continuous κ hκ k t ht).comp (values_continuous aRoot k)
  have hKi : Integrable K (Measure.pi (fun _=>haarAddCircle)) :=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK (w : Fin k→HeatCircle) : 0≤K w := by
    dsimp only [K]
    rw [←sum_density_eq κ hκ k t ht]
    exact Finset.sum_nonneg (fun Q _=>density_nonneg _ _)
  have hi (x : HeatCircle) : Integrable (fun w : Fin k→HeatCircle=>K w*|f (x+values aRoot k w j)|)
      (Measure.pi (fun _=>haarAddCircle)) :=
    hKi.mul_bdd ((continuous_abs.measurable.comp hf).comp
      (measurable_const.add ((continuous_apply j).measurable.comp (values_continuous aRoot k).measurable))).aestronglyMeasurable
      (ae_of_all _ (fun w=>by simpa only [Real.norm_eq_abs,abs_abs] using hfb (x+values aRoot k w j)))
  have hjoint : Measurable (fun z : HeatCircle×(Fin k→HeatCircle)=>K z.2*|f (z.1+values aRoot k z.2 j)|) :=
    (hKc.measurable.comp measurable_snd).mul ((continuous_abs.measurable.comp hf).comp
      (measurable_fst.add (((continuous_apply j).measurable.comp (values_continuous aRoot k).measurable).comp measurable_snd)))
  have hm := (hjoint.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _ : Fin k=>haarAddCircle))).measurable
  apply bounded_memLp (C:=(Fintype.card (Choices m k):ℝ)*B) hm
  intro x
  rw [abs_of_nonneg (integral_nonneg (fun w=>mul_nonneg (hK w) (abs_nonneg _)))]
  have hh := integral_mono (hi x) (hKi.mul_const B)
    (fun w=>mul_le_mul_of_nonneg_left (hfb (x+values aRoot k w j)) (hK w))
  simpa only [integral_mul_const,K,ForestedScoreInput.parentDensity_mass] using hh

/-- A finite sum of ORIGINAL leaf inputs passes through the genuine
positive parent forest. The spatial L2 gain is taken separately on each
input; there is no pointwise spatial supremum or independence premise. -/
theorem parent_leaf_sum_normTwo {ι : Type*} [Fintype ι] {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle)
    (j : ι→Fin (m+k)) (a : ι→ℝ) (ha : ∀ i,0≤a i)
    (f : ι→HeatCircle→ℝ) (hf : ∀ i,Measurable (f i))
    (B : ι→ℝ) (hB : ∀ i,0≤B i) (hfb : ∀ i x,|f i x|≤B i) :
    normTwo haarAddCircle (fun x=>∑ i,a i*∫ w : Fin k→HeatCircle,
      parentDensity κ hκ k t ht (values aRoot k w)*|f i (x+values aRoot k w (j i))|
        ∂Measure.pi (fun _=>haarAddCircle))≤
      (Fintype.card (Choices m k):ℝ)*∑ i,a i*normTwo haarAddCircle (f i) := by
  let G := fun i x=>∫ w : Fin k→HeatCircle,
    parentDensity κ hκ k t ht (values aRoot k w)*|f i (x+values aRoot k w (j i))|
      ∂Measure.pi (fun _=>haarAddCircle)
  have hG (i : ι) : MemLp (G i) 2 haarAddCircle :=
    parent_leaf_memLp κ hκ t ht aRoot (j i) (f i) (hf i) (hB i) (hfb i)
  have hh := normTwo_finset_sum Finset.univ (fun i x=>a i*G i x)
    (fun i _=>(hG i).const_mul (a i))
  refine hh.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [normTwo_const_mul (hG i) (a i),abs_of_nonneg (ha i)]
  have hb := ForestLeafInput.parent_leaf_normTwo κ hκ t ht aRoot (j i) (f i) (hf i) (hB i) (hfb i)
  convert! mul_le_mul_of_nonneg_left hb (ha i) using 1
  ring

end SHE.FiniteForestLeafInput
