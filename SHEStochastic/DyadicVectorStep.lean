module

public import SHEStochastic.L2EuclideanCoordinates
public import SHEStochastic.MatrixDyadicPairing
public import SHE.DyadicApproximation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.DyadicVectorStep
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation
open scoped ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
abbrev Physical := Lp (EuclideanSpace ℝ d) 2 μ

/-- Reuse the scalar physical dyadic steps and take their real part. -/
def realStep (n : ℕ) (a : Grid n → ℝ) : RealL2 :=
  Complex.reCLM.compLp (gridStep n a)

theorem realStep_ae (n : ℕ) (a : Grid n → ℝ) :
    ⇑(realStep n a) =ᵐ[μ] fun x => a (MatrixDyadicPairing.leaf n x) := by
  filter_upwards [Complex.reCLM.coeFn_compLp (gridStep n a), gridStep_ae_cellIndex n a] with x hr hs
  change Complex.reCLM.compLp (gridStep n a) x=_
  rw [hr, hs]
  rfl

def step (n : ℕ) (a : Grid n → EuclideanSpace ℝ d) : Physical (d := d) :=
  L2EuclideanCoordinates.reconstruction μ (WithLp.toLp 2 (fun i => realStep n (fun z => a z i)))

/-- The vector step has its literal cell value almost everywhere. -/
theorem step_ae (n : ℕ) (a : Grid n → EuclideanSpace ℝ d) :
    ⇑(step n a) =ᵐ[μ] fun x => a (MatrixDyadicPairing.leaf n x) := by
  have hr : ∀ᵐ x ∂μ, ∀ i : d,
      realStep n (fun z => a z i) x=a (MatrixDyadicPairing.leaf n x) i :=
    ae_all_iff.mpr (fun i => realStep_ae n (fun z => a z i))
  filter_upwards [L2EuclideanCoordinates.reconstruction_ae μ
    (WithLp.toLp 2 (fun i => realStep n (fun z => a z i))), hr] with x hx hr
  change L2EuclideanCoordinates.reconstruction μ
    (WithLp.toLp 2 (fun i => realStep n (fun z => a z i))) x=_
  rw [hx]
  ext i
  simp [L2EuclideanCoordinates.injection, hr, Pi.single_apply]

theorem realPart_realEmbed (u : RealL2) : Complex.reCLM.compLp (realEmbed u)=u := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp (realEmbed u), realEmbed_ae u] with x hr he
  rw [hr, he]
  rfl

theorem realStep_tendsto (u : RealL2) :
    Filter.Tendsto (fun n => realStep n (localAverage n (realEmbed u))) Filter.atTop (𝓝 u) := by
  have hh := (Complex.reCLM.compLpL 2 μ).continuous.tendsto (realEmbed u) |>.comp
    (average_realEmbed_tendsto u)
  change Filter.Tendsto (fun n => realStep n (localAverage n (realEmbed u)))
    Filter.atTop (𝓝 (Complex.reCLM.compLp (realEmbed u))) at hh
  rwa [realPart_realEmbed] at hh

/-- Componentwise dyadic approximation, using the already proved
scalar density theorem and the exact vector/component isometry. -/
theorem tendsto (u : Physical (d := d)) :
    Filter.Tendsto (fun n => step n (fun z => WithLp.toLp 2
      (fun i => localAverage n (realEmbed (L2EuclideanCoordinates.coordinates μ u i)) z)))
      Filter.atTop (𝓝 u) := by
  have hc : Filter.Tendsto (fun n => WithLp.toLp 2 (fun i : d =>
      realStep n (localAverage n (realEmbed (L2EuclideanCoordinates.coordinates μ u i)))))
      Filter.atTop (𝓝 (L2EuclideanCoordinates.coordinates μ u)) := by
    apply (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.tendsto _ |>.comp
      (tendsto_pi_nhds.mpr (fun i => realStep_tendsto (L2EuclideanCoordinates.coordinates μ u i)))
  have hh := (L2EuclideanCoordinates.reconstruction μ).continuous.tendsto
    (L2EuclideanCoordinates.coordinates μ u) |>.comp hc
  rw [L2EuclideanCoordinates.reconstruct_coordinates] at hh
  convert! hh using 1 <;> rfl

end SHEStochastic.DyadicVectorStep
