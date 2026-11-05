module

public import SHEStochastic.MatrixGlobalBlockBundle
public import SHE.DeterministicItoShiftClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixGlobalBlockFamily
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (hH0 : 0<H)

theorem law (k m : ℕ) (a : Fin m → Fin n×HaarNode) :
    FiniteBrownianLawOn (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H))
      (D.law ρ₀) H (fun i t p => CanonicalStateDriverFiltration.coordinate H (a i) t (MatrixGlobalBlockBundle.bundle H hH0 k p))
      (fun i j => if a i=a j then 1 else 0) := by
  constructor
  · intro t ht
    exact (MatrixFreshBlockBrownian.block_law D ρ₀ k m a t ht).comp
      (MatrixGlobalBlockBundle.preserving D ρ₀ (hH0 := hH0) k).hasLaw
  · intro s t hst ht
    have hi := (MatrixGlobalBrownianPast.brownian D ρ₀ hH0 (((k : ℝ≥0)*H)+H) m a).2
      (((k : ℝ≥0)*H)+s) (((k : ℝ≥0)*H)+t) (add_le_add le_rfl hst) (add_le_add le_rfl ht)
    have he : (fun p => WithLp.toLp 2 (fun i =>
        CanonicalStateDriverFiltration.coordinate H (a i) t (MatrixGlobalBlockBundle.bundle H hH0 k p)-
        CanonicalStateDriverFiltration.coordinate H (a i) s (MatrixGlobalBlockBundle.bundle H hH0 k p)))=
        MatrixGlobalBrownianPast.increments H a (((k : ℝ≥0)*H)+s) (((k : ℝ≥0)*H)+t) := by
      funext p
      apply PiLp.ext
      intro i
      change CanonicalStateDriverFiltration.coordinate H (a i) t (MatrixGlobalBlockBundle.bundle H hH0 k p)-
        CanonicalStateDriverFiltration.coordinate H (a i) s (MatrixGlobalBlockBundle.bundle H hH0 k p)=_
      dsimp only [MatrixGlobalBlockBundle.bundle]
      rw [CanonicalStateDriverFiltration.coordinate_bundle H _ _ _ _ _ t ht,
        CanonicalStateDriverFiltration.coordinate_bundle H _ _ _ _ _ s (hst.trans ht)]
      dsimp only [MatrixGlobalBrownianPast.increments,WithLp.ofLp_toLp]
      ring
    rw [he]
    exact hi

def family (k : ℕ) :
    FiniteScalarIto.Family (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H))
      (D.law ρ₀) H (Fin n×HaarNode) :=
  ⟨⟨(fun i t p => CanonicalStateDriverFiltration.coordinate H i t (MatrixGlobalBlockBundle.bundle H hH0 k p)),
    (fun i t => (CanonicalStateDriverFiltration.coordinate_adapted H i t).comp (MatrixGlobalBlockBundle.filtered H hH0 k t)),
    law D ρ₀ hH0 k⟩,fun i p => CanonicalStateDriverFiltration.coordinate_continuous H i (MatrixGlobalBlockBundle.bundle H hH0 k p)⟩

end SHEStochastic.MatrixGlobalBlockFamily
