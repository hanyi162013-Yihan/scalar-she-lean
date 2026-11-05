module

public import SHEStochastic.MatrixBlockContinuation
public import SHEStochastic.KernelMarkovLocalPast
public import SHEStochastic.KernelFixedStatisticLaw
public import SHE.BrownianShiftedFiniteLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixFreshBlockBrownian
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar CanonicalStateDriverFiltration
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))

def observations {m : ℕ} (a : Fin m → Fin n×HaarNode) (t : Fin m → ℝ≥0)
    (x : MatrixLocalBlockChain.Space (n := n) H) : SHE.WordRecursion.State m :=
  WithLp.toLp 2 (fun i => coordinate H (a i) (t i) x)

theorem observations_measurable {m : ℕ} (a : Fin m → Fin n×HaarNode) (t : Fin m → ℝ≥0) :
    Measurable (observations (H := H) a t) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
    (measurable_pi_lambda (fun i => (coordinate_adapted H (a i) (t i)).mono
      ((filtration H).le (t i)) le_rfl))

/-- Every selected block, including the initial block, has the same
finite Brownian driver laws after mixing over its random initial state. -/
theorem block_law (j m : ℕ) (a : Fin m → Fin n×HaarNode) (t : Fin m → ℝ≥0) (ht : ∀ i,t i≤H) :
    HasLaw (observations (H := H) a t)
      (multivariateGaussian (0 : SHE.WordRecursion.State m)
        (BrownianFiniteCovariance.matrix a t)) (D.blockLaw ρ₀ j).toMeasure := by
  let Q := (D.blockLaw ρ₀ j).toMeasure
  refine ⟨(observations_measurable a t).aemeasurable,?_⟩
  apply KernelFixedStatisticLaw.law (CanonicalInitialKernel.initialLaw H Q)
    (CanonicalInitialKernel.kernel H Q) Q (CanonicalInitialKernel.reconstruct H Q)
    (observations a t) (observations_measurable a t)
  filter_upwards [D.brownian (D.initialLaws ρ₀ j)] with z hz
  exact ((hz.choose m a).1 t ht).map_eq

/-- Every finite set of fresh local driver observations has its
Brownian Gaussian law jointly with every previous solution block. The
entire prefix, including all past states and drivers, is retained. -/
theorem prefix_law (j m : ℕ) (a : Fin m → Fin n×HaarNode) (t : Fin m → ℝ≥0) (ht : ∀ i,t i≤H) :
    (D.law ρ₀).map (fun p => (Preorder.frestrictLe j p,observations a t (p (j+1))))=
      ((D.law ρ₀).map (Preorder.frestrictLe j)).prod
        (multivariateGaussian (0 : SHE.WordRecursion.State m)
          (fun i l => (min (t i) (t l) : ℝ≥0)*(if a i=a l then 1 else 0 : ℝ))) := by
  apply KernelMarkovFreshLaw.prefix_product (D.blockLaw ρ₀ 0).toMeasure (D.kernel ρ₀) j
    (observations a t) (observations_measurable a t)
  change ∀ᵐ x ∂(D.law ρ₀).map (fun p => p j),_
  rw [D.marginals ρ₀ j]
  filter_upwards [MatrixBlockContinuation.future_brownian D ρ₀ j] with x hx
  exact ((hx.choose m a).1 t ht).map_eq

/-- The same fresh Gaussian law holds for the literal increments of
the globally pasted driver, rather than for an auxiliary block copy. -/
theorem pasted_prefix_law (hH0 : 0<H) (j m : ℕ) (a : Fin m → Fin n×HaarNode)
    (t : Fin m → ℝ≥0) (ht : ∀ i,t i≤H) :
    (D.law ρ₀).map (fun p => (Preorder.frestrictLe j p,WithLp.toLp 2 (fun i =>
      MatrixGlobalBlockPath.driver H (a i) (((j+1 : ℕ) : ℝ≥0)*H+t i) p-
        MatrixGlobalBlockPath.driver H (a i) (((j+1 : ℕ) : ℝ≥0)*H) p)))=
      ((D.law ρ₀).map (Preorder.frestrictLe j)).prod
        (multivariateGaussian (0 : SHE.WordRecursion.State m)
          (fun i l => (min (t i) (t l) : ℝ≥0)*(if a i=a l then 1 else 0 : ℝ))) := by
  refine Eq.trans (Measure.map_congr ?_) (prefix_law D ρ₀ j m a t ht)
  filter_upwards [MatrixBlockContinuation.driver_increment D ρ₀ hH0] with p hp
  congr 1
  apply PiLp.ext
  intro i
  exact hp (j+1) (a i) (t i) (ht i)

/-- Finite simultaneous increments within a fresh block. -/
def increments {m : ℕ} (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0)
    (x : MatrixLocalBlockChain.Space (n := n) H) : SHE.WordRecursion.State m :=
  WithLp.toLp 2 (fun i => coordinate H (a i) t x-coordinate H (a i) s x)

theorem increments_measurable {m : ℕ} (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0) :
    Measurable (increments (H := H) a s t) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
    (Measurable.of_eval (fun i =>
      ((coordinate_adapted H (a i) t).mono ((filtration H).le t) le_rfl).sub
        ((coordinate_adapted H (a i) s).mono ((filtration H).le s) le_rfl)))

/-- The finite Brownian past condition, in product-law form. -/
theorem local_past_product {Z : Type*} [MeasurableSpace Z]
    (Q : Measure (MatrixLocalBlockChain.Space (n := n) H)) [IsProbabilityMeasure Q]
    (hBrown : ∀ m (a : Fin m → Fin n×HaarNode),FiniteBrownianLawOn (filtration H) Q H
      (fun i => coordinate H (a i)) (fun i l => if a i=a l then 1 else 0))
    (m : ℕ) (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0) (hst : s≤t) (ht : t≤H)
    (g : MatrixLocalBlockChain.Space (n := n) H → Z) (hg : Measurable[filtration H s] g) :
    Q.map (fun x => (g x,increments (H := H) a s t x))=(Q.map g).prod
      (multivariateGaussian (0 : SHE.WordRecursion.State m)
        (BrownianFiniteCovariance.matrix a (fun _ => t-s))) := by
  have hgm : Measurable g := hg.mono ((filtration H).le s) le_rfl
  have him := increments_measurable (H := H) a s t
  have hLaw := BrownianShiftedFiniteLaw.law (filtration H) Q H
    (coordinate H) hBrown s (t-s) (by simpa only [add_tsub_cancel_of_le hst] using ht)
    a (fun _ => t-s) (fun _ => le_rfl)
  have hLaw' : HasLaw (increments (H := H) a s t)
      (multivariateGaussian (0 : SHE.WordRecursion.State m)
        (BrownianFiniteCovariance.matrix a (fun _ => t-s))) Q := by
    convert hLaw using 1
    funext ω
    apply PiLp.ext
    intro i
    simp only [increments,WithLp.ofLp_toLp,add_tsub_cancel_of_le hst]
  have hi : IndepFun g (increments (H := H) a s t) Q :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le_left ((hBrown m a).2 s t hst ht).symm (Measurable.comap_le hg))
  exact hi.map_prod_eq_prod_map_map hgm.aemeasurable him.aemeasurable |>.trans
    (congrArg (fun ν => (Q.map g).prod ν) hLaw'.map_eq)


/-- Fresh local increments are independent jointly of the complete
old prefix and ANY statistic measurable in the new block's local past.
This is the full-past property needed to paste Brownian drivers. -/
theorem prefix_local_past_law {Z : Type*} [MeasurableSpace Z]
    (j m : ℕ) (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0) (hst : s≤t) (ht : t≤H)
    (g : MatrixLocalBlockChain.Space (n := n) H → Z) (hg : Measurable[filtration H s] g) :
    (D.law ρ₀).map (fun p => ((Preorder.frestrictLe j p,g (p (j+1))),increments (H := H) a s t (p (j+1))))=
      ((D.law ρ₀).map (fun p => (Preorder.frestrictLe j p,g (p (j+1))))).prod
        (multivariateGaussian (0 : SHE.WordRecursion.State m)
          (BrownianFiniteCovariance.matrix a (fun _ => t-s))) := by
  have hgm : Measurable g := hg.mono ((filtration H).le s) le_rfl
  have him := increments_measurable (H := H) a s t
  apply KernelMarkovLocalPast.prefix_local_product (D.blockLaw ρ₀ 0).toMeasure (D.kernel ρ₀) j
    g hgm (increments (H := H) a s t) him
  change ∀ᵐ x ∂(D.law ρ₀).map (fun p => p j),_
  rw [D.marginals ρ₀ j]
  filter_upwards [MatrixBlockContinuation.future_brownian D ρ₀ j] with x hx
  exact local_past_product (D.kernel ρ₀ j x) hx.choose m a s t hst ht g hg

/-- Mixing over the initial state preserves the full local-past
increment property for every block, including block zero. -/
theorem block_local_past_law {Z : Type*} [MeasurableSpace Z]
    (j m : ℕ) (a : Fin m → Fin n×HaarNode) (s t : ℝ≥0) (hst : s≤t) (ht : t≤H)
    (g : MatrixLocalBlockChain.Space (n := n) H → Z) (hg : Measurable[filtration H s] g) :
    (D.blockLaw ρ₀ j).toMeasure.map (fun x => (g x,increments (H := H) a s t x))=
      ((D.blockLaw ρ₀ j).toMeasure.map g).prod
        (multivariateGaussian (0 : SHE.WordRecursion.State m)
          (BrownianFiniteCovariance.matrix a (fun _ => t-s))) := by
  let Q := (D.blockLaw ρ₀ j).toMeasure
  apply KernelFixedStatisticLaw.local_product (CanonicalInitialKernel.initialLaw H Q)
    (CanonicalInitialKernel.kernel H Q) Q (CanonicalInitialKernel.reconstruct H Q)
    g (hg.mono ((filtration H).le s) le_rfl) (increments (H := H) a s t)
    (increments_measurable a s t)
  filter_upwards [D.brownian (D.initialLaws ρ₀ j)] with z hz
  exact local_past_product (CanonicalInitialKernel.kernel H Q z) hz.choose m a s t hst ht g hg

end SHEStochastic.MatrixFreshBlockBrownian
