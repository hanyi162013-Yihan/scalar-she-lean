module

public import SHEStochastic.MatrixRowJets
public import SHEStochastic.VectorHeatPackets
public import SHE.HaarFinePacket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixFinePacket
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def scalarColumn (P : Profile d) (p : List Bool) (i r : d) (w : List (Domain (d := d))) : CircleHeat.CircleL2 :=
  realEmbed (component r (MatrixPhysicalJetStructure.jetColumn P p i w))

theorem mean_zero (P : Profile d) (p : List Bool) (i r : d) (w : List (Domain (d := d))) :
    inner ℂ circleOne (scalarColumn P p i r w) = 0 := by
  apply VectorHeatPackets.real_mean_zero
  have hh := VectorHeatPackets.coordinate_integral (MatrixPhysicalJetStructure.jetColumn P p i w) r
  rw [MatrixPhysicalJetStructure.mean_zero] at hh
  change (∫ x, component r (MatrixPhysicalJetStructure.jetColumn P p i w) x ∂μ) = 0
  convert! hh using 1

theorem supported (P : Profile d) (p : List Bool) (i r : d) (w : List (Domain (d := d))) :
    ∀ᵐ x ∂μ, x ∉ nodeCell p → scalarColumn P p i r w x = 0 := by
  filter_upwards [realEmbed_ae (component r (MatrixPhysicalJetStructure.jetColumn P p i w)),
    component_ae (MatrixPhysicalJetStructure.jetColumn P p i w) r,
    MatrixPhysicalJetStructure.supported P p i w] with x hr hc hs
  intro hn
  change realEmbed (component r (MatrixPhysicalJetStructure.jetColumn P p i w)) x = 0
  rw [hr, hc, hs hn]
  rfl

/-- The real physical vector derivative has the actual Gaussian heat
packet bound in each state component, with one negative input. -/
theorem pointwise {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t)
    (P : Profile d) (p : List Bool) (hsmall : nodeLength p ≤ Real.sqrt t) (i r : d)
    (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    ∀ᵐ x ∂μ, ‖CircleHeat.heat t (scalarColumn P p i r (v :: w)) x‖ ≤
      MatrixRowJets.packetConstant P ρ w.length * (NodeKernelLocal.constant p t ht x/(((2^(p.length+1):ℕ):ℝ))) *
        scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v * MatrixJetClosure.weight B w := by
  filter_upwards [HeatMarkov.kernel_inner_ae ht (scalarColumn P p i r (v :: w))] with x hx
  rw [← hx, ← centeredRow_pair p ht x _ (mean_zero P p i r (v :: w))]
  exact MatrixRowJets.packet hΛ hρ hρhalf P p (NodeKernelLocal.constant p t ht x)
    (NodeKernelLocal.constant_pos p ht x) (NodeKernelLocal.centeredRow p t ht x)
    (fun b y hy => NodeKernelLocal.row_amplitude p ht hsmall x b y hy)
    (fun b y hy z hz => NodeKernelLocal.row_lipschitz p ht hsmall x b y z hy hz)
    i r v w B hB hRest

end SHEStochastic.MatrixFinePacket
