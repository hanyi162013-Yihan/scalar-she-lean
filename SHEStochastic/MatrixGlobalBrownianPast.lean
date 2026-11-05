module

public import SHEStochastic.MatrixGlobalBlockIncrementLaw
public import SHEStochastic.MatrixGlobalBrownianFiniteLaw
public import SHEStochastic.GaussianPastAddition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixGlobalBrownianPast
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0)

def increments {m : ℕ} (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0)
    (p : MatrixGlobalBlockPath.Space (n := n) H) : WordRecursion.State m :=
  WithLp.toLp 2 (fun i => MatrixGlobalBlockPath.driver H (a i) t p-MatrixGlobalBlockPath.driver H (a i) s p)

theorem increments_adapted (hH : 0<H) {m : ℕ} (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hst : s≤t) :
    Measurable[MatrixBlockNaturalFiltration.filtration H t] (increments H a s t) := by
  let Ft := MatrixBlockNaturalFiltration.filtration (n := n) H t
  letI : MeasurableSpace (MatrixGlobalBlockPath.Space (n := n) H) := Ft
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
    (Measurable.of_eval (fun i =>
      (MatrixBlockProcessAdapted.driver_adapted H hH (a i) t).measurable.sub
        (((MatrixBlockProcessAdapted.driver_adapted H hH (a i) s).mono
          ((MatrixBlockNaturalFiltration.filtration H).mono hst)).measurable)))

variable {H} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

def ProductLaw {m : ℕ} (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0) : Prop :=
  (D.law ρ₀).map (fun p => (MatrixBlockNaturalFiltration.history H s p,increments H a s t p))=
    ((D.law ρ₀).map (MatrixBlockNaturalFiltration.history H s)).prod
      (multivariateGaussian (0 : WordRecursion.State m) (BrownianFiniteCovariance.matrix a (fun _ => t-s)))

theorem local_product (hH0 : 0<H) (k m : ℕ) (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hst : s≤t) (ht : t≤H) :
    ProductLaw D ρ₀ a ((k : ℝ≥0)*H+s) ((k : ℝ≥0)*H+t) := by
  have hh := MatrixGlobalBlockIncrementLaw.product_law D ρ₀ hH0 k m a s t hst ht
  have hd : ((k : ℝ≥0)*H+t)-((k : ℝ≥0)*H+s)=t-s := add_tsub_add_eq_tsub_left _ _ _
  simpa only [ProductLaw,increments,MatrixGlobalBlockIncrementLaw.increments,hd] using hh

/-- Full-past independence composes across a deterministic joining
time because the old increment and original past are measurable in
the physical filtration at that joining time. -/
theorem append (hH0 : 0<H) {m : ℕ} (a : Fin m → Fin n×HaarNode)
    (s v t : ℝ≥0) (hsv : s≤v) (hvt : v≤t)
    (hPast : ProductLaw D ρ₀ a s v) (hNext : ProductLaw D ρ₀ a v t) :
    ProductLaw D ρ₀ a s t := by
  let F := MatrixBlockNaturalFiltration.filtration (n := n) H
  let g := MatrixBlockNaturalFiltration.history (n := n) H s
  let x := increments H a s v
  let y := increments H a v t
  have hgF : Measurable[F v] g := (Measurable.of_comap_le (le_refl _) : Measurable[F s] g).mono (F.mono hsv) le_rfl
  have hxF : Measurable[F v] x := increments_adapted H hH0 a s v hsv
  have hg : Measurable g := hgF.mono (F.le v) le_rfl
  have hx : Measurable x := hxF.mono (F.le v) le_rfl
  have hy : Measurable y := (increments_adapted H hH0 a v t hvt).mono (F.le t) le_rfl
  let ν := multivariateGaussian (0 : WordRecursion.State m) (BrownianFiniteCovariance.matrix a (fun _ => t-v))
  obtain ⟨hi,hLaw⟩ := KernelFixedStatisticLaw.independent_of_product (D.law ρ₀)
    (MatrixBlockNaturalFiltration.history H v) y (MatrixBlockNaturalFiltration.history_measurable H v) hy ν hNext
  have hiS : Indep (F v) (MeasurableSpace.comap y inferInstance) (D.law ρ₀) :=
    (IndepFun_iff_Indep _ _ _).mp hi
  have hiP : IndepFun (fun p => (g p,x p)) y (D.law ρ₀) :=
    (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_left hiS ((hgF.prodMk hxF).comap_le))
  have hFresh := hiP.map_prod_eq_prod_map_map (hg.prodMk hx).aemeasurable hy.aemeasurable
  rw [hLaw.map_eq] at hFresh
  have hh := GaussianPastAddition.law (D.law ρ₀) g hg x y hx hy
    (BrownianFiniteCovariance.matrix a (fun _ => v-s)) (BrownianFiniteCovariance.matrix a (fun _ => t-v))
    (BrownianFiniteCovariance.posSemidef _ _) (BrownianFiniteCovariance.posSemidef _ _) hPast hFresh
  have hsum : (fun p => x p+y p)=increments H a s t := by
    funext p
    apply PiLp.ext
    intro i
    simp only [x,y,increments,PiLp.add_apply,WithLp.ofLp_toLp]
    ring
  have htime : (v-s)+(t-v)=t-s := (add_comm _ _).trans (tsub_add_tsub_cancel hvt hsv)
  have hcov : BrownianFiniteCovariance.matrix a (fun _ => v-s)+BrownianFiniteCovariance.matrix a (fun _ => t-v)=
      BrownianFiniteCovariance.matrix a (fun _ => t-s) := by
    ext i j
    simp only [Matrix.add_apply,BrownianFiniteCovariance.matrix,min_self]
    rw [←add_mul,←NNReal.coe_add,htime]
  have hsum' : ∀ p,x p+y p=increments H a s t p := congrFun hsum
  simp_rw [hsum'] at hh
  rw [hcov] at hh
  exact hh

/-- Arbitrarily many block boundaries retain the whole physical past,
not just the driver marginal distribution or endpoint state. -/
theorem product_bounded (hH0 : 0<H) (M m : ℕ) (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hst : s≤t) (ht : t≤(M+1 : ℕ)*H) : ProductLaw D ρ₀ a s t := by
  induction M generalizing s t with
  | zero =>
    have hh := local_product D ρ₀ hH0 0 m a s t hst (by simpa using ht)
    simpa only [Nat.cast_zero,zero_mul,zero_add] using hh
  | succ M ih =>
    let v : ℝ≥0 := (M+1 : ℕ)*H
    by_cases htv : t≤v
    · exact ih s t hst htv
    · have hvt : v≤t := le_of_not_ge htv
      have hlocal : t-v≤H := by
        apply tsub_le_iff_right.mpr
        calc
          t ≤ (M+1+1 : ℕ)*H := ht
          _ = H+v := by dsimp [v];push_cast;ring
      by_cases hsv : s≤v
      · have hNext := local_product D ρ₀ hH0 (M+1) m a 0 (t-v) bot_le hlocal
        change ProductLaw D ρ₀ a (v+0) (v+(t-v)) at hNext
        simp only [add_zero,add_tsub_cancel_of_le hvt] at hNext
        exact append D ρ₀ hH0 a s v t hsv hvt (ih s v hsv le_rfl) hNext
      · have hvs : v ≤ s := le_of_not_ge hsv
        have hh := local_product D ρ₀ hH0 (M+1) m a (s-v) (t-v) (tsub_le_tsub_right hst v) hlocal
        change ProductLaw D ρ₀ a (v+(s-v)) (v+(t-v)) at hh
        have hd : (t-v)-(s-v)=t-s := tsub_tsub_tsub_cancel_right hvs
        simpa only [ProductLaw,add_tsub_cancel_of_le hvs,add_tsub_cancel_of_le hvt,hd] using hh

theorem product (hH0 : 0<H) (m : ℕ) (a : Fin m → Fin n×HaarNode)
    (s t : ℝ≥0) (hst : s≤t) : ProductLaw D ρ₀ a s t :=
  product_bounded D ρ₀ hH0 ⌈t/H⌉₊ m a s t hst (CountablePathConcatenation.covering H t hH0)

/-- The constructed global driver is Brownian in the full physical
state-and-driver filtration on every finite horizon. -/
theorem brownian (hH0 : 0<H) (T : ℝ≥0) (m : ℕ) (a : Fin m → Fin n×HaarNode) :
    FiniteBrownianLawOn (MatrixBlockNaturalFiltration.filtration H) (D.law ρ₀) T
      (fun i => MatrixGlobalBlockPath.driver H (a i)) (fun i j => if a i=a j then 1 else 0) := by
  constructor
  · intro t _
    exact MatrixGlobalBrownianFiniteLaw.law_of_cover D ρ₀ hH0 m a t
  · intro s t hst _
    have hf : Measurable (increments H a s t) := (increments_adapted H hH0 a s t hst).mono
      ((MatrixBlockNaturalFiltration.filtration H).le t) le_rfl
    have hi := (KernelFixedStatisticLaw.independent_of_product (D.law ρ₀)
      (MatrixBlockNaturalFiltration.history H s) (increments H a s t)
      (MatrixBlockNaturalFiltration.history_measurable H s) hf
      (multivariateGaussian (0 : WordRecursion.State m) (BrownianFiniteCovariance.matrix a (fun _ => t-s)))
      (product D ρ₀ hH0 m a s t hst)).1
    exact ((IndepFun_iff_Indep _ _ _).mp hi).symm

/-- An actual all-coordinate Brownian family on the pasted solution
space, ready for the existing terminal Itô and mild-equation toolbox. -/
def family (hH0 : 0<H) (T : ℝ≥0) :
    FiniteScalarIto.Family (MatrixBlockNaturalFiltration.filtration H) (D.law ρ₀) T (Fin n×HaarNode) :=
  ⟨⟨MatrixGlobalBlockPath.driver H,
    (fun i t => (MatrixBlockProcessAdapted.driver_adapted H hH0 i t).measurable),brownian D ρ₀ hH0 T⟩,
      MatrixGlobalBlockPath.driver_continuous H hH0⟩

end SHEStochastic.MatrixGlobalBrownianPast
